#define _CRT_SECURE_NO_WARNINGS
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <cstdint>
#include <vector>
#include <string>
#include <algorithm>
#include <ctime>

using namespace std;

static const double RPI = 3.14159265358979323846;

static const int CBD[27] = { 0,1,2,3,4,5,6,7,9,11,13,15,17,20,23,27,31,37,43,51,62,74,89,110,139,180,256 };
static const int NCB = 26;
static const int MAXSC = 6;
static const int DCS = 512;
static const int HF = 256;
static const int Q = 128;
static const int MAXF = 256;
static const int BUF = 264;

static const char* MON[12] = { "Jan","Feb","Mar","Apr","May","Jun","Jul","Aug","Sep","Oct","Nov","Dec" };

static double SC[MAXSC], CO[Q], SI[Q], WN[DCS];
static double BETA;

static void init_tables() {
    SC[0] = 10.0;
    for (int i = 1; i < MAXSC; i++) SC[i] = SC[i - 1] * 10.0;
    for (int i = 0; i < MAXSC; i++) SC[i] = 1.0 / (double)((1 << (i + 1)) - 1) * SC[i];
    for (int i = 0; i < Q; i++) {
        double t = ((double)i + 0.125) * (RPI * 2.0) * (1.0 / (double)DCS);
        SI[i] = sin(t); CO[i] = cos(t);
    }
    for (int i = 0; i < DCS; i++) WN[i] = sin((double)i * (RPI / (double)DCS));
}

static void fft(float* re, float* im, int n) {
    for (int i = 1, j = 0; i < n; i++) {
        int bit = n >> 1;
        for (; j & bit; bit >>= 1) j ^= bit;
        j ^= bit;
        if (i < j) {
            float t = re[i]; re[i] = re[j]; re[j] = t;
            t = im[i]; im[i] = im[j]; im[j] = t;
        }
    }
    for (int len = 2; len <= n; len <<= 1) {
        double ang = -2.0 * RPI / (double)len;
        double wr = cos(ang), wi = sin(ang);
        int half = len >> 1;
        for (int i = 0; i < n; i += len) {
            double cr = 1.0, ci = 0.0;
            for (int k = 0; k < half; k++) {
                float ar = re[i + k], ai = im[i + k];
                float br = re[i + k + half], bi = im[i + k + half];
                float vr = (float)(br * cr - bi * ci);
                float vi = (float)(br * ci + bi * cr);
                re[i + k] = ar + vr; im[i + k] = ai + vi;
                re[i + k + half] = ar - vr; im[i + k + half] = ai - vi;
                double nr = cr * wr - ci * wi; ci = cr * wi + ci * wr; cr = nr;
            }
        }
    }
}

static void ifft(float* re, float* im, int n) {
    for (int i = 0; i < n; i++) im[i] = -im[i];
    fft(re, im, n);
    for (int i = 0; i < n; i++) { re[i] /= (float)n; im[i] = -im[i] / (float)n; }
}

static void apply_idct(const float* freq, float* wave) {
    float ire[Q], iim[Q], wt[DCS];
    for (int i = 0; i < Q; i++) {
        float c1 = freq[2 * i] * 0.5f;
        float c2 = freq[HF - 1 - 2 * i] * 0.5f;
        ire[i] = (float)(c1 * CO[i] + c2 * SI[i]);
        iim[i] = (float)(-c1 * SI[i] + c2 * CO[i]);
    }
    fft(ire, iim, Q);
    float f = (float)(8.0 / sqrt((double)DCS));
    for (int i = 0; i < Q; i++) {
        float x = ire[i], y = iim[i];
        wt[i * 2] = (float)((x * CO[i] + y * SI[i]) * f);
        wt[i * 2 + HF] = (float)((-x * SI[i] + y * CO[i]) * f);
    }
    for (int i = 1; i < DCS; i += 2) wt[i] = -wt[DCS - 1 - i];
    for (int i = 0; i < 3 * Q; i++) wave[i] = wt[Q + i];
    for (int i = 3 * Q; i < DCS; i++) wave[i] = -wt[i - 3 * Q];
}

static void apply_dct_fwd(const float* wave, float* freq) {
    float g[DCS], h[DCS], ur[Q], ui[Q];
    for (int i = 0; i < DCS; i++) g[i] = 0.0f;
    for (int j = 0; j < 3 * Q; j++) g[Q + j] += wave[j];
    for (int k = 0; k < Q; k++) g[k] -= wave[3 * Q + k];
    for (int j = 0; j < DCS; j += 2) h[j] = g[j] - g[DCS - 1 - j];
    float f = (float)(8.0 / sqrt((double)DCS));
    for (int i = 0; i < Q; i++) {
        float x = h[i * 2], y = h[i * 2 + HF];
        ur[i] = (float)((x * CO[i] - y * SI[i]) * f);
        ui[i] = (float)((x * SI[i] + y * CO[i]) * f);
    }
    ifft(ur, ui, Q);
    float s = (float)(BETA * Q);
    for (int i = 0; i < MAXF; i++) freq[i] = 0.0f;
    for (int i = 0; i < Q; i++) {
        float zr = ur[i] * s, zi = ui[i] * s;
        freq[2 * i] += (float)(0.5 * (CO[i] * zr - SI[i] * zi));
        freq[HF - 1 - 2 * i] += (float)(0.5 * (SI[i] * zr + CO[i] * zi));
    }
}

static void calibrate() {
    float e[MAXF], w[DCS];
    for (int i = 0; i < MAXF; i++) e[i] = 0.0f;
    e[0] = 1.0f;
    apply_idct(e, w);
    double a = 0.0;
    for (int i = 0; i < DCS; i++) a += (double)w[i] * (double)w[i];
    BETA = 2.0 / a;
}

struct BitW {
    vector<uint8_t> b;
    void init(int n) { b.assign(n, 0); }
    void put(uint32_t v, int bits, int off) {
        for (int i = 0; i < bits; i++) if ((v >> i) & 1) {
            int p = off + i;
            if ((p >> 3) >= (int)b.size()) b.resize((p >> 3) + 8, 0);
            b[p >> 3] |= (uint8_t)(1u << (p & 7));
        }
    }
};

static uint32_t getu(const uint8_t* p, int bits, int off) {
    int sh = off & 7, q = off >> 3;
    uint32_t v = 0;
    for (int k = 0; k < 4; k++) v |= (uint32_t)p[q + k] << (8 * k);
    return (v >> sh) & ((1u << bits) - 1);
}

static int gets(const uint8_t* p, int bits, int off) {
    uint32_t v = getu(p, bits, off);
    if ((v >> (bits - 1)) == 1) return -(int)(v & ((1u << (bits - 1)) - 1));
    return (int)v;
}

static int bcnt(uint32_t v) { int n = 0; while (v) { n++; v >>= 1; } return n; }

struct Ent { int pos, e, qv; double mag; };

struct Dec {
    float freq1[MAXF], freq2[MAXF];
    uint8_t exponents[MAXF];
    float wavecur[DCS], waveprv[DCS];
    void reset() {
        memset(exponents, 0, sizeof(exponents));
        memset(waveprv, 0, sizeof(waveprv));
        memset(wavecur, 0, sizeof(wavecur));
    }
};

static bool unpack_frame(const uint8_t* buf, int bufsize, Dec& d) {
    memset(d.freq1, 0, sizeof(d.freq1));
    memset(d.freq2, 0, sizeof(d.freq2));
    uint8_t flags = (uint8_t)getu(buf, 2, 0);
    uint8_t cb = (uint8_t)getu(buf, 3, 2);
    uint8_t ev = (uint8_t)getu(buf, 2, 5);
    uint8_t ei = (uint8_t)getu(buf, 4, 7);
    int bo = 11, maxo = bufsize * 8;
    if (flags & 1) memset(d.exponents, 0, MAXF);
    if (cb > 0 && ev > 0) {
        int pos = 0;
        for (int i = 0; i < NCB; i++) {
            if (bo + cb > maxo) return false;
            int mv = (int)getu(buf, cb, bo); bo += cb;
            if (i > 0 && mv == 0) break;
            pos += mv;
            if (bo + ev > maxo) return false;
            int e = (int)getu(buf, ev, bo); bo += ev;
            if (pos + 1 >= 27) return false;
            for (int j = CBD[pos]; j < CBD[pos + 1]; j++) d.exponents[j] = (uint8_t)e;
        }
    }
    if (ei > 0) {
        int pos = 0;
        for (int i = 0; i < MAXF; i++) {
            if (bo + ei > maxo) return false;
            int mv = (int)getu(buf, ei, bo); bo += ei;
            if (i > 0 && mv == 0) break;
            pos += mv;
            if (pos >= MAXF) return false;
            int qb = d.exponents[pos];
            if (bo + qb + 2 > maxo) return false;
            int qv = gets(buf, qb + 2, bo); bo += qb + 2;
            if (qv != 0 && pos < HF && qb < 6) d.freq1[pos] = (float)(qv * SC[qb]);
        }
        if (flags & 2) {
            memcpy(d.freq2, d.freq1, sizeof(d.freq1));
        }
        else {
            pos = 0;
            for (int i = 0; i < MAXF; i++) {
                if (bo + ei > maxo) return false;
                int mv = (int)getu(buf, ei, bo); bo += ei;
                if (i > 0 && mv == 0) break;
                pos += mv;
                if (pos >= MAXF) return false;
                int qb = d.exponents[pos];
                if (bo + qb + 2 > maxo) return false;
                int qv = gets(buf, qb + 2, bo); bo += qb + 2;
                if (qv != 0 && pos < HF && qb < 6) d.freq2[pos] = (float)(qv * SC[qb]);
            }
        }
    }
    float wt[DCS], wp[DCS], cur[DCS];
    memcpy(cur, d.waveprv, sizeof(cur));
    apply_idct(d.freq1, wt);
    apply_idct(d.freq2, wp);
    for (int i = 0; i < HF; i++) {
        cur[HF + i] = (float)(wt[i] * WN[i] + cur[HF + i] * WN[HF + i]);
        wp[i] = (float)(wp[i] * WN[i] + wt[HF + i] * WN[HF + i]);
    }
    memcpy(d.wavecur, cur, sizeof(cur));
    memcpy(d.waveprv, wp, sizeof(wp));
    return true;
}

static void decode_out(Dec& d, float* out) { memcpy(out, d.wavecur, DCS * sizeof(float)); }

static void quantize(const float* c1, const float* c2, uint8_t* expmap, vector<Ent>& a, vector<Ent>& b) {
    double m[NCB];
    for (int i = 0; i < NCB; i++) m[i] = 0.0;
    for (int k = 0; k < MAXF; k++) {
        double v1 = fabs((double)c1[k]), v2 = fabs((double)c2[k]);
        int bi = 0;
        for (int i = 0; i < NCB; i++) if (k >= CBD[i] && k < CBD[i + 1]) { bi = i; break; }
        if (v1 > m[bi]) m[bi] = v1;
        if (v2 > m[bi]) m[bi] = v2;
    }
    for (int i = 0; i < NCB; i++) {
        int e = 0;
        while (e < 5 && m[i] > pow(10.0, e + 1)) e++;
        for (int j = CBD[i]; j < CBD[i + 1]; j++) expmap[j] = (uint8_t)e;
    }
    a.clear(); b.clear();
    for (int k = 0; k < MAXF; k++) {
        int e = expmap[k];
        int lim = (1 << (e + 1)) - 1;
        int q1 = (int)floor((double)c1[k] / SC[e] + 0.5);
        int q2 = (int)floor((double)c2[k] / SC[e] + 0.5);
        if (q1 > lim) q1 = lim;
        if (q1 < -lim) q1 = -lim;
        if (q2 > lim) q2 = lim;
        if (q2 < -lim) q2 = -lim;
        if (q1 != 0) { Ent t; t.pos = k; t.e = e; t.qv = q1; t.mag = fabs((double)q1) * SC[e]; a.push_back(t); }
        if (q2 != 0) { Ent t; t.pos = k; t.e = e; t.qv = q2; t.mag = fabs((double)q2) * SC[e]; b.push_back(t); }
    }
}

static int cost_bits(const vector<Ent>& a, const vector<Ent>& b, const uint8_t* expmap, int cb, int ev, int ei) {
    int bits = 11;
    bits += NCB * (cb + ev) + cb;
    for (int t = 0; t < 2; t++) {
        const vector<Ent>& v = (t == 0) ? a : b;
        if (v.empty()) {
            bits += ei + (expmap[0] + 2) + ei;
            continue;
        }
        int pos = 0;
        for (size_t i = 0; i < v.size(); i++) {
            bits += ei;
            bits += expmap[v[i].pos] + 2;
            pos = v[i].pos;
        }
        (void)pos;
        if (v.size() < (size_t)MAXF) bits += ei;
    }
    return bits;
}

static void pack_frame(BitW& w, const vector<Ent>& a, const vector<Ent>& b, const uint8_t* expmap,
    int cb, int ev, int ei, int flags) {
    w.init(BUF);
    int off = 0;
    w.put((uint32_t)flags, 2, off); off += 2;
    w.put((uint32_t)cb, 3, off); off += 3;
    w.put((uint32_t)ev, 2, off); off += 2;
    w.put((uint32_t)ei, 4, off); off += 4;
    int pos = 0;
    for (int i = 0; i < NCB; i++) {
        int mv = (i == 0) ? 0 : 1;
        w.put((uint32_t)mv, cb, off); off += cb;
        pos += mv;
        w.put((uint32_t)expmap[CBD[pos]], ev, off); off += ev;
    }
    for (int t = 0; t < 2; t++) {
        const vector<Ent>& v = (t == 0) ? a : b;
        if (v.empty()) {
            w.put(0, ei, off); off += ei;
            w.put(0, expmap[0] + 2, off); off += expmap[0] + 2;
            w.put(0, ei, off); off += ei;
            continue;
        }
        int p = 0;
        for (size_t i = 0; i < v.size(); i++) {
            int mv = (i == 0) ? v[i].pos : (v[i].pos - p);
            w.put((uint32_t)mv, ei, off); off += ei;
            int bits = expmap[v[i].pos] + 2;
            int lim = (1 << (bits - 1)) - 1;
            int q = v[i].qv;
            uint32_t enc;
            if (q < 0) enc = (uint32_t)(((-q) & lim) | (1u << (bits - 1)));
            else enc = (uint32_t)q;
            w.put(enc, bits, off); off += bits;
            p = v[i].pos;
        }
        if (v.size() < (size_t)MAXF) { w.put(0, ei, off); off += ei; }
    }
}

struct Frame { BitW w; };

static void encode_frame(float* c1, float* c2, uint8_t* expmap, BitW& w, int budget, int& usedbits) {
    vector<Ent> a, b;
    quantize(c1, c2, expmap, a, b);
    int cb = 1, ev = 3;
    int maxgap = 1;
    for (int t = 0; t < 2; t++) {
        const vector<Ent>& v = (t == 0) ? a : b;
        int p = 0;
        for (size_t i = 0; i < v.size(); i++) {
            int g = (i == 0) ? (v[i].pos + 1) : (v[i].pos - p);
            if (g > maxgap) maxgap = g;
            p = v[i].pos;
        }
    }
    int ei = bcnt((uint32_t)maxgap);
    if (ei < 1) ei = 1;
    if (ei > 15) ei = 15;

    if (cost_bits(a, b, expmap, cb, ev, ei) > budget) {
        vector<pair<double, int> > ord;
        for (size_t i = 0; i < a.size(); i++) ord.push_back(make_pair(a[i].mag, -(int)i - 1));
        for (size_t i = 0; i < b.size(); i++) ord.push_back(make_pair(b[i].mag, (int)i + 1));
        sort(ord.begin(), ord.end());
        vector<char> da(a.size(), 0), db(b.size(), 0);
        size_t drop = 0;
        while (drop < ord.size()) {
            int idx = ord[drop].second;
            if (idx < 0) da[-idx - 1] = 1; else db[idx - 1] = 1;
            drop++;
            vector<Ent> ra, rb;
            for (size_t i = 0; i < a.size(); i++) if (!da[i]) ra.push_back(a[i]);
            for (size_t i = 0; i < b.size(); i++) if (!db[i]) rb.push_back(b[i]);
            int mg = 1;
            for (int t = 0; t < 2; t++) {
                const vector<Ent>& v = (t == 0) ? ra : rb;
                int p = 0;
                for (size_t i = 0; i < v.size(); i++) {
                    int g = (i == 0) ? (v[i].pos + 1) : (v[i].pos - p);
                    if (g > mg) mg = g;
                    p = v[i].pos;
                }
            }
            ei = bcnt((uint32_t)mg);
            if (ei < 1) ei = 1;
            if (ei > 15) ei = 15;
            if (cost_bits(ra, rb, expmap, cb, ev, ei) <= budget) {
                a.swap(ra); b.swap(rb);
                break;
            }
            if (drop == ord.size()) { a.swap(ra); b.swap(rb); break; }
        }
    }
    pack_frame(w, a, b, expmap, cb, ev, ei, 1);
    usedbits = cost_bits(a, b, expmap, cb, ev, ei);
}

struct Wav {
    int ch;
    int rate;
    int bits;
    vector<float> pcm;
    Wav() : ch(0), rate(0), bits(0) {}
};

static bool read_wav(const char* fn, Wav& w) {
    FILE* f = fopen(fn, "rb");
    if (!f) return false;
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    vector<uint8_t> d(n);
    if (fread(d.data(), 1, n, f) != (size_t)n) { fclose(f); return false; }
    fclose(f);
    if (n < 44 || memcmp(d.data(), "RIFF", 4) || memcmp(d.data() + 8, "WAVE", 4)) return false;
    int fmt = 0, ch = 0, rate = 0, bits = 0;
    long off = 12;
    while (off + 8 <= n) {
        uint32_t id = (uint32_t)d[off] | ((uint32_t)d[off + 1] << 8) | ((uint32_t)d[off + 2] << 16) | ((uint32_t)d[off + 3] << 24);
        uint32_t sz = (uint32_t)d[off + 4] | ((uint32_t)d[off + 5] << 8) | ((uint32_t)d[off + 6] << 16) | ((uint32_t)d[off + 7] << 24);
        long body = off + 8;
        if (id == 0x20746d66) {
            fmt = d[body] | (d[body + 1] << 8);
            ch = d[body + 2] | (d[body + 3] << 8);
            rate = (int)((uint32_t)d[body + 4] | ((uint32_t)d[body + 5] << 8) | ((uint32_t)d[body + 6] << 16) | ((uint32_t)d[body + 7] << 24));
            bits = d[body + 14] | (d[body + 15] << 8);
        }
        else if (id == 0x61746164) {
            int bps = bits / 8;
            size_t cnt = sz / (size_t)bps;
            w.pcm.resize(cnt);
            for (size_t i = 0; i < cnt; i++) {
                int16_t s = (int16_t)(d[body + i * bps] | (d[body + i * bps + 1] << 8));
                w.pcm[i] = (float)s;
            }
        }
        off = body + sz + (sz & 1);
    }
    w.ch = ch; w.rate = rate; w.bits = bits;
    return fmt == 1 && ch >= 1 && ch <= 2 && bits == 16 && rate == 44100;
}

static void wr_be32(vector<uint8_t>& o, uint32_t v) {
    o.push_back((uint8_t)(v >> 24)); o.push_back((uint8_t)(v >> 16)); o.push_back((uint8_t)(v >> 8)); o.push_back((uint8_t)v);
}
static void wr_be16(vector<uint8_t>& o, uint32_t v) { o.push_back((uint8_t)(v >> 8)); o.push_back((uint8_t)v); }
static void wr_le32(vector<uint8_t>& o, uint32_t v) {
    o.push_back((uint8_t)v); o.push_back((uint8_t)(v >> 8)); o.push_back((uint8_t)(v >> 16)); o.push_back((uint8_t)(v >> 24));
}
static void wr_tag(vector<uint8_t>& o, const char* s) { for (int i = 0; i < 4; i++) o.push_back((uint8_t)s[i]); }

static void write_aifc(const char* fn, int ch, int frames, int blockrate, const vector<uint8_t>& audio) {
    vector<uint8_t> o;
    wr_tag(o, "FORM");
    size_t fsz = o.size(); wr_be32(o, 0);
    wr_tag(o, "AIFC");
    wr_tag(o, "FVER"); wr_be32(o, 4); wr_be32(o, 0xA2805140u);
    wr_tag(o, "COMM"); wr_be32(o, 39);
    wr_be16(o, (uint32_t)ch);
    wr_be32(o, (uint32_t)frames);
    wr_be16(o, 16);
    static const uint8_t ext[10] = { 0x40,0x0e,0xac,0x44,0x00,0x00,0x00,0x00,0x00,0x00 };
    for (int i = 0; i < 10; i++) o.push_back(ext[i]);
    wr_tag(o, "COMP");
    o.push_back(16);
    const char* nm = "Relic Codec v1.6";
    for (int i = 0; i < 16; i++) o.push_back((uint8_t)nm[i]);
    o.push_back(0);
    wr_tag(o, "SSND");
    wr_be32(o, (uint32_t)(8 + 2 + (int)audio.size()));
    wr_be32(o, 0); wr_be32(o, 0);
    wr_be16(o, (uint32_t)blockrate);
    for (size_t i = 0; i < audio.size(); i++) o.push_back(audio[i]);
    uint32_t total = (uint32_t)(o.size() - 8);
    o[fsz] = (uint8_t)(total >> 24); o[fsz + 1] = (uint8_t)(total >> 16); o[fsz + 2] = (uint8_t)(total >> 8); o[fsz + 3] = (uint8_t)total;
    FILE* f = fopen(fn, "wb");
    fwrite(o.data(), 1, o.size(), f);
    fclose(f);
}

static void write_fda(const char* fn, int ch, int blockrate, const vector<uint8_t>& audio) {
    vector<uint8_t> o;
    const uint8_t magic[16] = { 'R','e','l','i','c',' ','C','h','u','n','k','y','\r','\n',0x1a,0x00 };
    for (int i = 0; i < 16; i++) o.push_back(magic[i]);
    wr_le32(o, 1); wr_le32(o, 1);
    vector<uint8_t> burn;
    {
        const char* s1 = "RAW to FDA";
        const char* s2 = "relic_enc.exe";
        char s3[32];
        time_t t = time(NULL);
        struct tm* tm = localtime(&t);
        snprintf(s3, sizeof(s3), "%s %2d, %4d, %d:%02d:%02d %s",
            MON[tm->tm_mon],
            tm->tm_mday, tm->tm_year + 1900,
            (tm->tm_hour % 12 == 0) ? 12 : (tm->tm_hour % 12), tm->tm_min, tm->tm_sec,
            tm->tm_hour < 12 ? "AM" : "PM");
        char s3p[25];
        memset(s3p, ' ', 25);
        int L = (int)strlen(s3); if (L > 25) L = 25;
        memcpy(s3p, s3, L);
        wr_le32(burn, 10); for (int i = 0; i < 10; i++) burn.push_back((uint8_t)s1[i]);
        wr_le32(burn, 1);
        wr_le32(burn, 13); for (int i = 0; i < 13; i++) burn.push_back((uint8_t)s2[i]);
        wr_le32(burn, 25); for (int i = 0; i < 25; i++) burn.push_back((uint8_t)s3p[i]);
    }
    wr_tag(o, "DATA"); wr_tag(o, "FBIF"); wr_le32(o, 1); wr_le32(o, (uint32_t)burn.size()); wr_le32(o, 13);
    const char* bn = "FileBurnInfo";
    for (int i = 0; i < 12; i++) o.push_back((uint8_t)bn[i]);
    o.push_back(0);
    for (size_t i = 0; i < burn.size(); i++) o.push_back(burn[i]);

    uint32_t infolen = 28, datalen = 4 + (uint32_t)audio.size();
    uint32_t foldsz = 20 + infolen + 20 + datalen;
    wr_tag(o, "FOLD"); wr_tag(o, "FDA "); wr_le32(o, 1); wr_le32(o, foldsz); wr_le32(o, 0);
    wr_tag(o, "DATA"); wr_tag(o, "INFO"); wr_le32(o, 1); wr_le32(o, infolen); wr_le32(o, 0);
    wr_le32(o, (uint32_t)ch); wr_le32(o, 16); wr_le32(o, (uint32_t)blockrate); wr_le32(o, 44100);
    wr_le32(o, 0); wr_le32(o, 0xFFFFFFFFu); wr_le32(o, 0);
    wr_tag(o, "DATA"); wr_tag(o, "DATA"); wr_le32(o, 1); wr_le32(o, datalen); wr_le32(o, 0);
    wr_le32(o, (uint32_t)audio.size());
    for (size_t i = 0; i < audio.size(); i++) o.push_back(audio[i]);
    FILE* f = fopen(fn, "wb");
    fwrite(o.data(), 1, o.size(), f);
    fclose(f);
}

int main(int argc, char** argv) {
    if (argc < 3) {
        printf("Usage: relic_enc <wav_file> <aifc|fda_file> [block_bitrate]\n");
        return 1;
    }
    init_tables();
    calibrate();

    Wav w;
    if (!read_wav(argv[1], w)) {
        printf("Error: need 16-bit PCM WAV, mono/stereo, 44100 Hz\n");
        return 1;
    }
    int blockrate = (argc > 3) ? atoi(argv[3]) : 2048;
    blockrate = (blockrate / 8) * 8;
    if (blockrate < 256) blockrate = 256;
    if (blockrate > 2048) blockrate = 2048;
    int framesize = blockrate / 8;
    int ch = w.ch;
    int ns = (int)w.pcm.size() / ch;
    int nframes = (ns + 511) / 512;
    int nblocks = 2 * nframes;

    vector<vector<float> > sig(ch);
    for (int c = 0; c < ch; c++) {
        sig[c].assign((size_t)nblocks * 256 + 512, 0.0f);
        for (size_t m = 0; m < sig[c].size(); m++) {
            long src = (long)m + 256;
            if (src < ns) sig[c][m] = w.pcm[(size_t)src * ch + c];
        }
    }

    vector<uint8_t> audio;
    audio.reserve((size_t)nframes * framesize * ch);
    vector<uint8_t> buf(BUF);
    double totbits = 0.0;

    for (int fr = 0; fr < nframes; fr++) {
        for (int c = 0; c < ch; c++) {
            float c1[MAXF], c2[MAXF];
            float blk[DCS];
            int b0 = 2 * fr;
            for (int i = 0; i < DCS; i++) blk[i] = sig[c][(size_t)b0 * 256 + i] * (float)WN[i];
            apply_dct_fwd(blk, c1);
            for (int i = 0; i < DCS; i++) blk[i] = sig[c][(size_t)(b0 + 1) * 256 + i] * (float)WN[i];
            apply_dct_fwd(blk, c2);

            uint8_t expmap[MAXF];
            BitW wri;
            int used = 0;
            encode_frame(c1, c2, expmap, wri, framesize * 8, used);
            totbits += used;
            for (int i = 0; i < framesize; i++) audio.push_back(wri.b[i]);
        }
    }

    string out = argv[2];
    bool isfda = false;
    if (out.size() > 4) {
        string e = out.substr(out.size() - 4);
        if (e == ".fda" || e == ".FDA") isfda = true;
    }
    if (isfda) write_fda(argv[2], ch, blockrate, audio);
    else write_aifc(argv[2], ch, ns / 512, blockrate, audio);

    printf("Encoded %s -> %s\n", argv[1], argv[2]);
    printf("  channels=%d rate=%d samples=%d frames=%d\n", ch, w.rate, ns, nframes);
    printf("  block_bitrate=%d frame_size=%d avg_bits=%.1f (%.1f%%)\n",
        blockrate, framesize, totbits / (double)((size_t)nframes * ch), 100.0 * totbits / (double)((size_t)nframes * ch * framesize * 8));

    vector<Dec> dec(ch);
    for (int c = 0; c < ch; c++) dec[c].reset();
    size_t off = 0;
    vector<float> outall((size_t)nframes * 512 * ch, 0.0f);
    for (int fr = 0; fr < nframes; fr++) {
        float outb[2][DCS];
        for (int c = 0; c < ch; c++) {
            memcpy(buf.data(), audio.data() + off, framesize);
            memset(buf.data() + framesize, 0, BUF - framesize);
            off += framesize;
            if (!unpack_frame(buf.data(), BUF, dec[c])) { printf("  decode error at frame %d ch %d\n", fr, c); break; }
            decode_out(dec[c], outb[c]);
        }
        for (int s = 0; s < 512; s++)
            for (int c = 0; c < ch; c++) outall[((size_t)fr * 512 + s) * ch + c] = outb[c][s];
    }
    int bestlag = 0; double bestsnr = -1e18;
    for (int lag = -128; lag <= 384; lag++) {
        double e = 0, g = 0; long n = 0;
        for (long i = 256; i < (long)nframes * 512 - 512; i++) {
            long src = i - lag;
            if (src < 256 || src >= ns) continue;
            for (int c = 0; c < ch; c++) {
                double y = (double)w.pcm[(size_t)src * ch + c];
                double x = outall[(size_t)i * ch + c];
                e += (x - y) * (x - y); g += y * y; n++;
            }
        }
        if (n > 0 && g > 0) {
            double s = 10.0 * log10(g / (e > 0 ? e : 1e-9));
            if (s > bestsnr) { bestsnr = s; bestlag = lag; }
        }
    }
    printf("  round-trip SNR = %.2f dB at lag %d (interior)\n", bestsnr, bestlag);
    return 0;
}