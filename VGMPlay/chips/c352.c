// license:BSD-3-Clause
// copyright-holders:R. Belmont, superctr
/*
    c352.c - Namco C352 custom PCM chip emulation
    v2.0
    By R. Belmont
    Rewritten and improved by superctr
    Additional code by cync and the hoot development team

    Thanks to Cap of VivaNonno for info and The_Author for preliminary reverse-engineering

    Chip specs:
    32 voices
    Supports 8-bit linear and 8-bit muLaw samples
    Output: digital, 16 bit, 4 channels
    Output sample rate is the input clock / (288 * 2).
 */

//#include "emu.h"
//#include "streams.h"

#ifdef _WIN32
#include <io.h>
#define access _access
#else
#include <unistd.h>
#endif


#include <math.h>
#include <stdlib.h>
#include <string.h> // for memset
#include <stddef.h> // for NULL
#include <stdio.h>
#include "mamedef.h"
#include "c352.h"

#define C352_VOICES 32
enum {
    C352_FLG_BUSY       = 0x8000,   // channel is busy
    C352_FLG_KEYON      = 0x4000,   // Keyon
    C352_FLG_KEYOFF     = 0x2000,   // Keyoff
    C352_FLG_LOOPTRG    = 0x1000,   // Loop Trigger
    C352_FLG_LOOPHIST   = 0x0800,   // Loop History
    C352_FLG_FM         = 0x0400,   // Frequency Modulation
    C352_FLG_PHASERL    = 0x0200,   // Rear Left invert phase 180 degrees
    C352_FLG_PHASEFL    = 0x0100,   // Front Left invert phase 180 degrees
    C352_FLG_PHASEFR    = 0x0080,   // invert phase 180 degrees (e.g. flip sign of sample)
    C352_FLG_LDIR       = 0x0040,   // loop direction
    C352_FLG_LINK       = 0x0020,   // "long-format" sample (can't loop, not sure what else it means)
    C352_FLG_NOISE      = 0x0010,   // play noise instead of sample
    C352_FLG_MULAW      = 0x0008,   // sample is mulaw instead of linear 8-bit PCM
    C352_FLG_FILTER     = 0x0004,   // don't apply filter
    C352_FLG_REVLOOP    = 0x0003,   // loop backwards
    C352_FLG_LOOP       = 0x0002,   // loop forward
    C352_FLG_REVERSE    = 0x0001    // play sample backwards
};

typedef struct {

    UINT32 pos;
    UINT32 counter;

    INT16 sample;
    INT16 last_sample;

    UINT16 vol_f;
    UINT16 vol_r;
    UINT8 curr_vol[4];
    UINT16 freq;
    UINT16 flags;

    UINT16 wave_bank;
    UINT16 wave_start;
    UINT16 wave_end;
    UINT16 wave_loop;

    UINT8 mute;

} C352_Voice;

typedef struct {

    UINT32 sample_rate_base;
    UINT16 divider;

    C352_Voice v[C352_VOICES];

    UINT16 random;
    UINT16 control; // control flags, purpose unknown.

    UINT8* wave;
    UINT32 wavesize;
    UINT32 wave_mask;

    UINT8 muteRear;     // flag from VGM header
    //UINT8 optMuteRear;  // option
    
    UINT16 mulaw_table[256];

} C352;

typedef struct{
    UINT32 wave_origin;
    UINT32 wave_curr;
    UINT8 active;
    UINT8 ch; //pointer
    UINT16 flags; //need to save
    UINT16 freq; //important information
}smpl_search;
static smpl_search sample_search;

static UINT8 mulaw_remap[256];
    
typedef struct{
    UINT32 wave_origin;
    UINT32 wave_last;
    UINT16 flags; //need to save
    UINT16 freq; //important information
}tracked_sample;

static tracked_sample tracked_samples[0x80];
static UINT8 total_tracked = 0;

#define MAX_CHIPS   0x02
static C352 C352Data[MAX_CHIPS];

static UINT8 MuteAllRear = 0x00;

//static FILE *long_smpl_debug;

static void register_untracked_sample(UINT32 wave_origin, UINT32 wave_last, UINT16 flags, UINT16 freq){

    if(total_tracked == 0){//register sample
        tracked_samples[0].wave_origin = wave_origin;
        tracked_samples[0].wave_last = wave_last;
        tracked_samples[0].flags = flags;
        tracked_samples[0].freq = freq;
        total_tracked += 1;
    }
    else
    {
        if(total_tracked >= 0x80)
            return;
        for(int i = 0; i < total_tracked; i++){
            if(tracked_samples[i].wave_origin == wave_origin){ //don't register, just update
                tracked_samples[i].wave_last = tracked_samples[i].wave_last > wave_last ?
                    tracked_samples[i].wave_last : wave_last;
                return;
            }
        }
        //sample hasn't been registered yet, ok
        tracked_samples[total_tracked].wave_origin = wave_origin;
        tracked_samples[total_tracked].wave_last = wave_last;
        tracked_samples[total_tracked].flags = flags;
        tracked_samples[total_tracked].freq = freq;
        total_tracked += 1;
    }

}

UINT8 linear_to_mulaw(INT16 sample)
{
    //this code was borrowed from https://github.com/escrichov/G711/blob/master/g711.c
    //only relevant modification is the conversion of the scaled magnitude to segment number
    
    INT16 mask, seg;
    UINT8 uval;

    sample = sample >> 2;
    if (sample >= 0) mask = 0xFF;		
    else {
        mask = 0x7F;		
        sample = -sample;
    }
    
    if (sample > 0x1FDF) 
        sample = 0x1FDF; //clip magnitude
    sample += (0x84 >> 2); //literally just 0x21, but it's fine for a small scope program
    /* Convert the scaled magnitude to segment number. */
    INT16 test = 0x3f;
    for(seg = 0; seg < 8; seg++, test = (test << 1)|1)
    {
        //this replaces a lookup table and a function a call from the original
        if (sample <= test)
            break;
    }
    /*
    * Combine the sign, segment, quantization bits,
    * and complement the code word.
    */
    if (seg >= 8)		/* out of range, return maximum value. */
        return (UINT8)(0x7F ^ mask);
    else {
        uval = (UINT8)(seg << 4) | ((sample >> (seg + 1)) & 0xF);
        return (uval ^ mask);
    }
}

void c352_export_sample(C352* chip, C352_Voice* voice){
    
    char filebuf[32];
	snprintf(filebuf, 32, "c352_%08x.wav", voice->pos);
    if (access(filebuf, F_OK) == 0)
        return;
    FILE *outFile = fopen(filebuf, "wb");
    if (outFile == NULL) {
        perror("Error while opening file.");
        exit(1);
    }

    C352_Voice v = *voice;
    
    int length = 0;
    UINT8 sample;
    
    INT32 loop = -1;
    size_t header_size = sizeof(RIFFHeader) + sizeof(fmtHeader) + sizeof(dataHeader);
    if(v.flags & C352_FLG_MULAW){
        header_size = sizeof(RIFFHeader) + sizeof(nonPCMfmtHeader) + sizeof(factHeader) + sizeof(dataHeader);
    }
    fwrite(&loop, 1, header_size, outFile);
    
    while (v.flags & C352_FLG_BUSY)
    {
        UINT16 pos = v.pos & 0xffff;

        // --- read sample ---
        sample = (chip->wave[v.pos & chip->wave_mask]);
        if ((v.flags & C352_FLG_MULAW))
            sample = mulaw_remap[sample & 0xff];
        else
            sample += 0x80;
            
        // --- advance position / handle boundaries ---
        if((v.flags & C352_FLG_LOOP) && (v.flags & C352_FLG_REVERSE))
        {
            if(pos == v.wave_end){
                //v->flags |= C352_FLG_KEYOFF;
                v.flags &= ~C352_FLG_BUSY;
            }
            else
                v.pos += 1;
        }
        else if(pos == v.wave_end)
        {
            v.flags &= ~C352_FLG_BUSY;
            
        }
        else
        {
            v.pos += (v.flags & C352_FLG_REVERSE) ? -1 : 1;
        }
        fwrite(&sample, sizeof(UINT8), 1, outFile);
        length++;
    }

    if(length & 1){ //necessary padding for 8-bit PCM when length is odd
        sample = 0x80;
        fwrite(&sample, sizeof(UINT8), 1, outFile);
    }

    //WRITE HEADERS
    if (v.flags & C352_FLG_LOOP){
        loop = ((v.pos&0xff0000) | v.wave_loop) - (voice->pos);
    }

    UINT32 smpl_rate = (UINT32)(v.freq)*(1.3451);
    
    smplHeader smpl;
    strncpy(smpl.subchunk3ID, "smpl", 4);
    smpl.subchunk3Size = 36 + (loop >= 0) * sizeof(smplLoop);
    smpl.dwManufacturer = smpl.dwProduct = smpl.dwMIDIPitchFraction =
        smpl.dwSMPTEFormat = smpl.dwSMPTEOffset = smpl.cbSamplerData = 0;
    smpl.dwSamplePeriod = (UINT32)(1E9 / smpl_rate);
    smpl.dwMIDIUnityNote = 60;
    smpl.cSampleLoops = (loop >= 0);
    fwrite(&smpl, sizeof(smpl), 1, outFile);
    
    if (loop >= 0) {
        smplLoop L;
        L.dwIdentifier = 0;
        L.dwType = (v.flags & C352_FLG_REVERSE);
        L.dwStart = loop;
        L.dwEnd = (length)-1;
        L.dwFraction = 0;
        L.dwPlayCount = 0;
        fwrite(&L, sizeof(L), 1, outFile);
    }
    
    RIFFHeader riffHeader;
    fmtHeader fmtHeader;
    nonPCMfmtHeader nonPCMfmt;
    factHeader fact;
    dataHeader dataHeader;
    
    memset(&riffHeader, 0, sizeof(riffHeader));
    memset(&fmtHeader, 0, sizeof(fmtHeader));
    memset(&nonPCMfmt, 0, sizeof(nonPCMfmt));
    memset(&fact, 0, sizeof(fact));
    memset(&dataHeader, 0, sizeof(dataHeader));
    
    strncpy(riffHeader.chunkID, "RIFF", 4);
    // Total file size minus 8 (ID and Size fields)
    riffHeader.chunkSize = ftell(outFile) - 8;
    strncpy(riffHeader.format, "WAVE", 4);

    fseek(outFile, 0, SEEK_SET);
    fwrite(&riffHeader, sizeof(riffHeader), 1, outFile);

    if (v.flags & C352_FLG_MULAW) {
        strncpy(nonPCMfmt.subchunk1ID, "fmt ", 4);
        nonPCMfmt.subchunk1Size = 18;
        nonPCMfmt.audioFormat = 7;
        nonPCMfmt.numChannels = 1;
        nonPCMfmt.sampleRate = smpl_rate;
        nonPCMfmt.bitsPerSample = 8;
        nonPCMfmt.byteRate = smpl_rate * nonPCMfmt.numChannels * nonPCMfmt.bitsPerSample / 8;
        nonPCMfmt.blockAlign = (nonPCMfmt.numChannels * nonPCMfmt.bitsPerSample) / 8;
        nonPCMfmt.cbSize = 0;
        fwrite(&nonPCMfmt, sizeof(nonPCMfmt), 1, outFile);

        strncpy(fact.factID, "fact", 4);
        fact.factSize = 4;
        fact.dwSampleLength = length;
        fwrite(&fact, sizeof(fact), 1, outFile);
    }
    else {
        strncpy(fmtHeader.subchunk1ID, "fmt ", 4);
        fmtHeader.subchunk1Size = 16;
        fmtHeader.audioFormat = 1;
        fmtHeader.numChannels = 1;
        fmtHeader.sampleRate = smpl_rate;
        fmtHeader.bitsPerSample = 8;
        fmtHeader.byteRate = smpl_rate * fmtHeader.numChannels * fmtHeader.bitsPerSample / 8;
        fmtHeader.blockAlign = (fmtHeader.numChannels * fmtHeader.bitsPerSample) / 8;
        fwrite(&fmtHeader, sizeof(fmtHeader), 1, outFile);
    }
    
    strncpy(dataHeader.subchunk2ID, "data", 4);
    dataHeader.subchunk2Size = length;
    fwrite(&dataHeader, sizeof(dataHeader), 1, outFile);
    
    fclose(outFile);
}

void C352_exportLONGsample(C352* chip, UINT32 end_addr){

    char filebuf[32];
	snprintf(filebuf, 32, "c352_%08x.wav", sample_search.wave_origin);
    FILE *outFile = fopen(filebuf, "wb");
    if (outFile == NULL) {
        perror("Error while opening file.");
        exit(1);
    }

    int length = 0;
    UINT8 sample;

    INT32 loop = -1;
    size_t header_size = sizeof(RIFFHeader) + sizeof(fmtHeader) + sizeof(dataHeader);
    if(sample_search.flags & C352_FLG_MULAW){
        header_size = sizeof(RIFFHeader) + sizeof(nonPCMfmtHeader) + sizeof(factHeader) + sizeof(dataHeader);
    }
    fwrite(&loop, 1, header_size, outFile);

    for (UINT32 addr = sample_search.wave_origin; addr <= end_addr; addr++, length++){
        
        sample = (chip->wave[addr & chip->wave_mask]);
        if ((sample_search.flags & C352_FLG_MULAW))
            sample = mulaw_remap[sample & 0xff];
        else
            sample += 0x80;

        fwrite(&sample, 1, 1, outFile);
    }

    //WRITE HEADERS
    if(length & 1){ //necessary padding for 8-bit PCM when length is odd
        sample = 0x80;
        fwrite(&sample, sizeof(UINT8), 1, outFile);
    }

    UINT32 smpl_rate = (UINT32)(sample_search.freq)*(1.3451);
    
    smplHeader smpl;
    strncpy(smpl.subchunk3ID, "smpl", 4);
    smpl.subchunk3Size = 36 + (loop >= 0) * sizeof(smplLoop);
    smpl.dwManufacturer = smpl.dwProduct = smpl.dwMIDIPitchFraction =
        smpl.dwSMPTEFormat = smpl.dwSMPTEOffset = smpl.cbSamplerData = 0;
    smpl.dwSamplePeriod = (UINT32)(1E9 / smpl_rate);
    smpl.dwMIDIUnityNote = 60;
    smpl.cSampleLoops = (loop >= 0);
    fwrite(&smpl, sizeof(smpl), 1, outFile);
    
    if (loop >= 0) {
        smplLoop L;
        L.dwIdentifier = 0;
        L.dwType = (sample_search.flags & C352_FLG_REVERSE);
        L.dwStart = loop;
        L.dwEnd = (length) - 1;
        L.dwFraction = 0;
        L.dwPlayCount = 0;
        fwrite(&L, sizeof(L), 1, outFile);
    }
    
    RIFFHeader riffHeader;
    fmtHeader fmtHeader;
    nonPCMfmtHeader nonPCMfmt;
    factHeader fact;
    dataHeader dataHeader;
    
    memset(&riffHeader, 0, sizeof(riffHeader));
    memset(&fmtHeader, 0, sizeof(fmtHeader));
    memset(&nonPCMfmt, 0, sizeof(nonPCMfmt));
    memset(&fact, 0, sizeof(fact));
    memset(&dataHeader, 0, sizeof(dataHeader));
    
    strncpy(riffHeader.chunkID, "RIFF", 4);
    // Total file size minus 8 (ID and Size fields)
    riffHeader.chunkSize = ftell(outFile) - 8;
    strncpy(riffHeader.format, "WAVE", 4);

    fseek(outFile, 0, SEEK_SET);
    fwrite(&riffHeader, sizeof(riffHeader), 1, outFile);

    if (sample_search.flags & C352_FLG_MULAW) {
        strncpy(nonPCMfmt.subchunk1ID, "fmt ", 4);
        nonPCMfmt.subchunk1Size = 18;
        nonPCMfmt.audioFormat = 7;
        nonPCMfmt.numChannels = 1;
        nonPCMfmt.sampleRate = smpl_rate;
        nonPCMfmt.bitsPerSample = 8;
        nonPCMfmt.byteRate = smpl_rate * nonPCMfmt.numChannels * nonPCMfmt.bitsPerSample / 8;
        nonPCMfmt.blockAlign = (nonPCMfmt.numChannels * nonPCMfmt.bitsPerSample) / 8;
        nonPCMfmt.cbSize = 0;
        fwrite(&nonPCMfmt, sizeof(nonPCMfmt), 1, outFile);

        strncpy(fact.factID, "fact", 4);
        fact.factSize = 4;
        fact.dwSampleLength = length;
        fwrite(&fact, sizeof(fact), 1, outFile);
    }
    else {
        strncpy(fmtHeader.subchunk1ID, "fmt ", 4);
        fmtHeader.subchunk1Size = 16;
        fmtHeader.audioFormat = 1;
        fmtHeader.numChannels = 1;
        fmtHeader.sampleRate = smpl_rate;
        fmtHeader.bitsPerSample = 8;
        fmtHeader.byteRate = smpl_rate * fmtHeader.numChannels * fmtHeader.bitsPerSample / 8;
        fmtHeader.blockAlign = (fmtHeader.numChannels * fmtHeader.bitsPerSample) / 8;
        fwrite(&fmtHeader, sizeof(fmtHeader), 1, outFile);
    }
    
    strncpy(dataHeader.subchunk2ID, "data", 4);
    dataHeader.subchunk2Size = length;
    fwrite(&dataHeader, sizeof(dataHeader), 1, outFile);
    
    fclose(outFile);

}

void export_missing_samples(C352* chip){
    for(int i = 0; i < total_tracked; i++){
        char filebuf[32];
        snprintf(filebuf, 32, "c352_%08x.wav", tracked_samples[i].wave_origin);
        if (access(filebuf, F_OK) == 0)
            continue;
        //reuse sample_search, since it's used in the code,
        //and I don't feel like touching it again
        sample_search.wave_origin = tracked_samples[i].wave_origin;
        sample_search.flags = tracked_samples[i].flags;
        sample_search.freq = tracked_samples[i].freq;
        C352_exportLONGsample(chip, tracked_samples[i].wave_last);
    }
}

static void C352_fetch_sample(C352 *c, C352_Voice *v)
{
    v->last_sample = v->sample;
    
    if(v->flags & C352_FLG_NOISE)
    {
        c->random = (c->random>>1) ^ ((-(c->random&1)) & 0xfff6);
        v->sample = c->random;
    }
    else
    {
        INT8 s;
        UINT16 pos;

        s = (INT8)c->wave[v->pos & c->wave_mask];

        v->sample = s<<8;
        if(v->flags & C352_FLG_MULAW)
        {
            v->sample = c->mulaw_table[s&0xff];
        }
        
        pos = v->pos&0xffff;
        
        if((v->flags & C352_FLG_LOOP) && v->flags & C352_FLG_REVERSE)
        {
            // backwards>forwards
            if((v->flags & C352_FLG_LDIR) && pos == v->wave_loop)
                v->flags &= ~C352_FLG_LDIR;
            // forwards>backwards
            else if(!(v->flags & C352_FLG_LDIR) && pos == v->wave_end)
                v->flags |= C352_FLG_LDIR;
            
            v->pos += (v->flags&C352_FLG_LDIR) ? -1 : 1;
        }
        else if(pos == v->wave_end)
        {
            if((v->flags & C352_FLG_LINK) && (v->flags & C352_FLG_LOOP))
            {
                v->pos = (v->wave_start<<16) | v->wave_loop;
                if(sample_search.active && (&(c->v[sample_search.ch]) == v))
                {    
                    sample_search.wave_curr = v->pos;
                }
                v->flags |= C352_FLG_LOOPHIST;
            }
            else if(v->flags & C352_FLG_LOOP)
            {
                v->pos = (v->pos&0xff0000) | v->wave_loop;
                v->flags |= C352_FLG_LOOPHIST;
            }
            else
            {
                v->flags |= C352_FLG_KEYOFF;
                v->flags &= ~C352_FLG_BUSY;
                v->sample=0;
            }
        }
        else
        {
            v->pos += (v->flags&C352_FLG_REVERSE) ? -1 : 1;
        }
    }
}

static void c352_ramp_volume(C352_Voice* v,int ch,UINT8 val)
{
    INT16 vol_delta = v->curr_vol[ch] - val;
    if(vol_delta != 0)
        v->curr_vol[ch] += (vol_delta>0) ? -1 : 1;
}

void c352_update(UINT8 ChipID, stream_sample_t **outputs, int samples)
{
    C352 *c = &C352Data[ChipID];
    int i, j;
    INT16 s;
    INT32 next_counter;
    C352_Voice* v;

    stream_sample_t out[4];

    memset(outputs[0], 0, samples * sizeof(stream_sample_t));
    memset(outputs[1], 0, samples * sizeof(stream_sample_t));

    for(i=0;i<samples;i++)
    {
        out[0]=out[1]=out[2]=out[3]=0;

        for(j=0;j<C352_VOICES;j++)
        {

            v = &c->v[j];
            s = 0;

            if(v->flags & C352_FLG_BUSY)
            {
                next_counter = v->counter+v->freq;

                if(next_counter & 0x10000)
                {
                    C352_fetch_sample(c,v);
                }

                if((next_counter^v->counter) & 0x18000)
                {
                    c352_ramp_volume(v,0,v->vol_f>>8);
                    c352_ramp_volume(v,1,v->vol_f&0xff);
                    c352_ramp_volume(v,2,v->vol_r>>8);
                    c352_ramp_volume(v,3,v->vol_r&0xff);
                }

                v->counter = next_counter&0xffff;

                s = v->sample;

                // Interpolate samples
                if((v->flags & C352_FLG_FILTER) == 0)
                    s = v->last_sample + (v->counter*(v->sample-v->last_sample)>>16);
            }
            else if(
                (v->flags & C352_FLG_LINK) 
                && sample_search.active 
                && sample_search.ch == j
                
            ){
                register_untracked_sample(
                    sample_search.wave_origin,
                    v->pos,
                    sample_search.flags,
                    sample_search.freq
                );
                
                sample_search.active = 0;
                sample_search.ch = 32;
                sample_search.wave_origin = sample_search.wave_curr = 0;
            }

            if(!c->v[j].mute)
            {
                // Left
                out[0] += (((v->flags & C352_FLG_PHASEFL) ? -s : s) * v->curr_vol[0])>>8;
                out[2] += (((v->flags & C352_FLG_PHASERL) ? -s : s) * v->curr_vol[2])>>8;

                // Right
                out[1] += (((v->flags & C352_FLG_PHASEFR) ? -s : s) * v->curr_vol[1])>>8;
                out[3] += (((v->flags & C352_FLG_PHASEFR) ? -s : s) * v->curr_vol[3])>>8;
            }
        }

        outputs[0][i] += out[0];
        outputs[1][i] += out[1];
        if (!c->muteRear && !MuteAllRear)
        {
            outputs[0][i] += out[2];
            outputs[1][i] += out[3];
        }
    }
}

int device_start_c352(UINT8 ChipID, int clock, int clkdiv)
{
    C352 *c;
    int i,j;

    if (ChipID >= MAX_CHIPS)
        return 0;

    c = &C352Data[ChipID];

    c->wave = NULL;
    c->wavesize = 0x00;

    c->divider = clkdiv ? clkdiv : 288;
    c->sample_rate_base = (clock&0x7FFFFFFF) / c->divider;
    c->muteRear = (clock&0x80000000)>>31;

    memset(c->v,0,sizeof(C352_Voice)*C352_VOICES);

    c352_set_mute_mask(ChipID, 0x00000000);
    
    j=0;
    for(i=0;i<128;i++)
    {
        c->mulaw_table[i] = j<<5;
        if(i < 16)
            j += 1;
        else if(i < 24)
            j += 2;
        else if(i < 48)
            j += 4;
        else if(i < 100)
            j += 8;
        else
            j += 16;
        mulaw_remap[i] = linear_to_mulaw(c->mulaw_table[i]);
    }
    for(i=128;i<256;i++){
        c->mulaw_table[i] = (~c->mulaw_table[i-128])&0xffe0;
        mulaw_remap[i] = linear_to_mulaw(c->mulaw_table[i]);
    }
    //long_smpl_debug = fopen("debug.txt", "w");
    
    sample_search.active = 0;
    sample_search.ch = 32;
    sample_search.wave_origin = sample_search.wave_curr = 0;

    return c->sample_rate_base;
}

void device_stop_c352(UINT8 ChipID)
{
    C352 *c = &C352Data[ChipID];
    export_missing_samples(c);

    //fclose(long_smpl_debug);
    
    free(c->wave);
    c->wave = NULL;
    
    return;
}

void device_reset_c352(UINT8 ChipID)
{
    C352 *c = &C352Data[ChipID];
    UINT32 muteMask;
    
    muteMask = c352_get_mute_mask(ChipID);
    
    // clear all channels states
    memset(c->v,0,sizeof(C352_Voice)*C352_VOICES);
    
    // init noise generator
    c->random = 0x1234;
    c->control = 0;
    
    c352_set_mute_mask(ChipID, muteMask);
    
    return;
}

static UINT16 C352RegMap[8] = {
    offsetof(C352_Voice,vol_f) / sizeof(UINT16),
    offsetof(C352_Voice,vol_r) / sizeof(UINT16),
    offsetof(C352_Voice,freq) / sizeof(UINT16),
    offsetof(C352_Voice,flags) / sizeof(UINT16),
    offsetof(C352_Voice,wave_bank) / sizeof(UINT16),
    offsetof(C352_Voice,wave_start) / sizeof(UINT16),
    offsetof(C352_Voice,wave_end) / sizeof(UINT16),
    offsetof(C352_Voice,wave_loop) / sizeof(UINT16),
};

UINT16 c352_r(UINT8 ChipID, offs_t address)
{
    C352 *c = &C352Data[ChipID];

    if(address < 0x100)
        return *((UINT16*)&c->v[address/8]+C352RegMap[address%8]);
    else if(address == 0x200)
        return c->control;
    else
        return 0;
}

void c352_w(UINT8 ChipID, offs_t address, UINT16 val)
{
    C352 *c = &C352Data[ChipID];
    
    int i;
    
    if(address < 0x100) // Channel registers, see map above.
    {
        *((UINT16*)&c->v[address/8]+C352RegMap[address%8]) = val;
    }
    else if(address == 0x200)
    {
        c->control = val;
        //logerror("C352 control register write: %04x\n",val);
    }
    else if(address == 0x202) // execute keyons/keyoffs
    {
        for(i=0;i<C352_VOICES;i++)
        {
            if(sample_search.active && (i == sample_search.ch)){
                UINT16 temp = c->v[i].flags & (C352_FLG_KEYON|C352_FLG_KEYOFF);
                if(temp){
                    register_untracked_sample(
                        sample_search.wave_origin,
                        c->v[i].pos, 
                        sample_search.flags,
                        sample_search.freq
                    );
                    //RESET SEARCH
                    sample_search.active = 0;
                    sample_search.ch = 32;
                    sample_search.wave_origin = sample_search.wave_curr = 0;

                }
            }
            if((c->v[i].flags & C352_FLG_KEYON))
            {

                c->v[i].pos = (c->v[i].wave_bank<<16) | c->v[i].wave_start;

                c->v[i].sample = 0;
                c->v[i].last_sample = 0;
                c->v[i].counter = 0xffff;

                c->v[i].flags |= C352_FLG_BUSY;
                c->v[i].flags &= ~(C352_FLG_KEYON|C352_FLG_LOOPHIST);

                c->v[i].curr_vol[0] = c->v[i].curr_vol[1] = 0;
                c->v[i].curr_vol[2] = c->v[i].curr_vol[3] = 0;
                
                if(!(c->v[i].flags & C352_FLG_LINK))
                {
                    c352_export_sample(c, &(c->v[i]));
                }
                else
                {
                    char filebuf[32];
	                snprintf(filebuf, 32, "c352_%08x.wav", c->v[i].pos);
                    if(access(filebuf, F_OK) != 0) //file doesn't exist? good
                    {    
                        if(!sample_search.active){
                            //c352_dump_linked_sample(c, &(c->v[i]));
                            sample_search.active = 1; //START!!!
                            sample_search.ch = i;
                            sample_search.wave_origin = sample_search.wave_curr = c->v[i].pos;
                            sample_search.flags = c->v[i].flags;
                            sample_search.freq = c->v[i].freq;
                        }
                    }
                }
                
                
            }
            else if(c->v[i].flags & C352_FLG_KEYOFF)
            {
                c->v[i].flags &= ~(C352_FLG_BUSY|C352_FLG_KEYOFF);
                c->v[i].counter = 0xffff;
            }
        }
    }
}


void c352_write_rom(UINT8 ChipID, offs_t ROMSize, offs_t DataStart, offs_t DataLength,
                    const UINT8* ROMData)
{
    C352 *c = &C352Data[ChipID];
    
    if (c->wavesize != ROMSize)
    {
        c->wave = (UINT8*)realloc(c->wave, ROMSize);
        c->wavesize = ROMSize;
        for (c->wave_mask = 1; c->wave_mask < c->wavesize; c->wave_mask <<= 1)
            ;
        c->wave_mask --;
        memset(c->wave, 0xFF, ROMSize);
    }
    if (DataStart > ROMSize)
        return;
    if (DataStart + DataLength > ROMSize)
        DataLength = ROMSize - DataStart;
    
    memcpy(c->wave + DataStart, ROMData, DataLength);
    
    return;
}

void c352_set_mute_mask(UINT8 ChipID, UINT32 MuteMask)
{
    C352 *c = &C352Data[ChipID];
    UINT8 CurChn;
    
    for (CurChn = 0; CurChn < C352_VOICES; CurChn ++)
        c->v[CurChn].mute = (MuteMask >> CurChn) & 0x01;
    
    return;
}

UINT32 c352_get_mute_mask(UINT8 ChipID)
{
    C352 *c = &C352Data[ChipID];
    UINT32 muteMask;
    UINT8 CurChn;
    
    muteMask = 0x00000000;
    for (CurChn = 0; CurChn < C352_VOICES; CurChn ++)
        muteMask |= (c->v[CurChn].mute << CurChn);
    
    return muteMask;
}

void c352_set_options(UINT8 Flags)
{
    MuteAllRear = (Flags & 0x01) >> 0;
    
    return;
}

