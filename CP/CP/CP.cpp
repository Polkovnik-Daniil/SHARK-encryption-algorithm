#include <map>
#include <iostream>
#include <fstream> 
#include <string> 

using namespace std;

#define ROUNDS 6
#define LENGTHKEY 16
#define LENGTHVOCUBALARY 258*8
#define ROUNDKEYS ROUNDS+1
#define ROOT 0x1f5
#define FILENAMEENCRYPT "ENCRYPT.txt"
#define FILENAMEFORENCRYPT "FORREADENCRYPT.txt"
#define FILENAMEVOCUBALARY "VOCUB.txt"
#define FILENAMEDECRYPT "DECRYPT.txt"

typedef unsigned char byte;
typedef unsigned long ulong;
char filenameforencrypt[] = "FORREADENCRYPT.txt";

string ReadFileForEncrypt();

typedef struct ddword {
    union {
        ulong w[2];
        byte b[8];
    };
};

ddword operator ^ (ddword x, ddword y) {
    x.w[0] ^= y.w[0];
    x.w[1] ^= y.w[1];
    return x;
}

struct diffusion {
    byte log[256], alog[256], G[8][8], iG[8][8];
    byte mul(byte a, byte b); /* multiply two elements of GF(2^m) */
    void transform(ddword& a);
    diffusion();
};

struct coder {
    ddword buf;
    ddword roundkey[ROUNDKEYS];
    ddword cbox[8][256];
    byte sbox[256];
    void do_block();
};

struct shark {
    coder enc, dec;
    shark(byte* key, unsigned key_length);
    ddword encryption(ddword plain);
    ddword decryption(ddword cipher);
};

byte diffusion::mul(byte a, byte b) /* multiply two elements of GF(2^m */
{
    if(a && b) 
        return alog[(log[a] + log[b]) % 255];
    else return 0;
}

diffusion::diffusion() {
    unsigned i, j = 1;
    for(i = 0; i < 256; i++) {
        alog[i] = j;
        j *= 2;
        if(j & 0x100) 
            j ^= ROOT;
    }
    log[0] = 0;
    log[1] = 0; // N.B.
    for(i = 1; i < 255; i++)
        log[alog[i]] = i;

    byte g[9], c[9];
    byte A[8][16];

    /* diffusion box G
     * g(x) = (x - 2)*(x - 4)*...*(x - 2^{8})
     * the rows of G are the coefficients of
     * x^{i} mod g(x), i = 2n - 1, 2n - 2, ..., n
     * iG = inv(G)
     * A = [G,I]
     * Gauss elemination on A to produce [I,iG]
     */
    g[0] = 2;
    g[1] = 1;
    for(i = 2; i < 9; i++) g[i] = 0;
    for(i = 2; i <= 8; i++) {
        for(j = 8; j > 0; j--) {
            if(g[j]) g[j] = g[j - 1] ^ alog[(i + log[g[j]]) % 255];
            else g[j] = g[j - 1];
        }
        g[0] = alog[(i + log[g[0]]) % 255];
    }

    for(j = 0; j < 8; j++) c[j] = 0;
    c[8] = 1;
    for(i = 0; i < 8; i++) {
        if(c[8])
            for(byte u = 1; u <= 8; u++)
                c[8 - u] ^= mul(c[8], g[8 - u]);
        c[8] = 0;
        for(j = 0; j < 8; j++)
            G[7 - i][7 - j] = c[j];
        for(j = 8; j > 0; j--)
            c[j] = c[j - 1];
        c[0] = 0;
    }

    for(i = 0; i < 8; i++) {
        for(j = 0; j < 8; j++) A[i][j] = G[i][j];
        for(j = 8; j < 16; j++) A[i][j] = 0;
        A[i][i + 8] = 1;
    }
    for(i = 0; i < 8; i++) {
        byte pivot = A[i][i];
        if(pivot == 0) {
            unsigned t = i + 1;
            while(A[t][i] == 0) 
                if(t < 8)
                    t += 1;
            for(j = 0; j < 16; j++) {
                byte tmp = A[i][j];
                A[i][j] = A[t][j];
                A[t][j] = tmp;
            }
            pivot = A[i][i];
        }
        for(j = 0; j < 16; j++) {
            if(A[i][j])
                A[i][j] = alog[(255 + log[A[i][j]] - log[pivot]) % 255];
        }
        for(unsigned t = 0; t < 8; t++) {
            if(i != t) {
                for(j = i + 1; j < 16; j++)
                    A[t][j] ^= mul(A[i][j], A[t][i]);
                A[t][i] = 0;
            }
        }
    }
    for(i = 0; i < 8; i++)
        for(j = 0; j < 8; j++) iG[i][j] = A[i][j + 8];

}

void diffusion::transform(ddword& a) {
    unsigned i, j;
    ddword k = a;
    for(i = 0; i < 8; i++) {
        byte sum = 0;
        for(j = 0; j < 8; j++) sum ^= mul(iG[i][j], k.b[7 - j]);
        a.b[7 - i] = sum;
    }
}

void coder::do_block() {
    ulong t, w0, w1 = buf.w[1];
    for(unsigned r = 0; r < ROUNDS - 1; r += 1) {
        unsigned ix;
        t = w1 ^ roundkey[r].w[1];
        ix = (unsigned)t % 256; w0 = cbox[3][ix].w[0]; w1 = cbox[3][ix].w[1]; t /= 256;
        ix = (unsigned)t % 256; w0 ^= cbox[2][ix].w[0]; w1 ^= cbox[2][ix].w[1]; t /= 256;
        ix = (unsigned)t % 256; w0 ^= cbox[1][ix].w[0]; w1 ^= cbox[1][ix].w[1]; t /= 256;
        ix = (unsigned)t; w0 ^= cbox[0][ix].w[0]; w1 ^= cbox[0][ix].w[1];
        t = buf.w[0] ^ roundkey[r].w[0];
        ix = (unsigned)t % 256; w0 ^= cbox[7][ix].w[0]; w1 ^= cbox[7][ix].w[1]; t /= 256;
        ix = (unsigned)t % 256; w0 ^= cbox[6][ix].w[0]; w1 ^= cbox[6][ix].w[1]; t /= 256;
        ix = (unsigned)t % 256; w0 ^= cbox[5][ix].w[0]; w1 ^= cbox[5][ix].w[1]; t /= 256;
        ix = (unsigned)t; w0 ^= cbox[4][ix].w[0]; w1 ^= cbox[4][ix].w[1];
        buf.w[0] = w0;
    }

    t = w1 ^ roundkey[ROUNDS - 1].w[1];
    w1 = sbox[t % 256];       t /= 256;
    w1 |= sbox[t % 256] << 8; t /= 256;
    w1 |= sbox[t % 256] << 16; t /= 256;
    w1 |= sbox[t] << 24;
    buf.w[1] = w1 ^ roundkey[ROUNDS].w[1];

    t = buf.w[0] ^ roundkey[ROUNDS - 1].w[0];
    w0 = sbox[t % 256];       t /= 256;
    w0 |= sbox[t % 256] << 8; t /= 256;
    w0 |= sbox[t % 256] << 16; t /= 256;
    w0 |= sbox[t] << 24;
    buf.w[0] = w0 ^ roundkey[ROUNDS].w[0];
}

ddword shark::encryption(ddword plain) {
    enc.buf = plain;
    enc.do_block();
    return enc.buf;
}

ddword shark::decryption(ddword cipher) {
    dec.buf = cipher;
    dec.do_block();
    return dec.buf;
}

shark::shark(byte* key, unsigned key_length) {
    diffusion diff;
    {  // initialise boxes
        byte trans[9] = { 0xd6, 0x7b, 0x3d, 0x1f, 0x0f, 0x05, 0x03, 0x01, 0xb1 };
        unsigned i, j, k;
        /* the substitution box based on F^{-1}(x + affine transform of the output */
        enc.sbox[0] = 0;
        enc.sbox[1] = 1;
        for(i = 2; i < 256; i++) enc.sbox[i] = diff.alog[255 - diff.log[i]];

        for(i = 0; i < 256; i++) {
            byte in = enc.sbox[i];
            enc.sbox[i] = 0;
            for(unsigned t = 0; t < 8; t++) {
                byte u = in & trans[t];
                enc.sbox[i] ^= ((1 & (u ^ (u >> 1) ^ (u >> 2) ^ (u >> 3)
                                ^ (u >> 4) ^ (u >> 5) ^ (u >> 6) ^ (u >> 7)))
                                << (7 - t));
            }
            enc.sbox[i] ^= trans[8];
        }

        for(i = 0; i < 256; i++) dec.sbox[enc.sbox[i]] = i;

        for(j = 0; j < 8; j++)
            for(k = 0; k < 256; k++)
                for(i = 0; i < 8; i++) {
                    enc.cbox[j][k].b[7 - i] = diff.mul(enc.sbox[k], diff.G[i][j]);
                    dec.cbox[j][k].b[7 - i] = diff.mul(dec.sbox[k], diff.iG[i][j]);
                }
    }

    { // initialise roundkeys
        ddword a[ROUNDKEYS];
        unsigned i, j, r;

        for(r = 0; r <= ROUNDS; r++) enc.roundkey[r] = enc.cbox[0][r];
        diff.transform(enc.roundkey[ROUNDS]);

        i = 0;
        for(r = 0; r < ROUNDKEYS; r++)
            for(j = 0; j < 8; j++)
                a[r].b[7 - j] = key[(i++) % key_length];

        ddword temp[ROUNDKEYS];
        ddword zero; zero.w[0] = 0; zero.w[1] = 0;
        temp[0] = a[0] ^ encryption(zero);
        for(r = 1; r < ROUNDKEYS; r += 1)
            temp[r] = a[r] ^ encryption(temp[r - 1]);
        diff.transform(temp[ROUNDS]);

        for(r = 0; r < ROUNDKEYS; r += 1) {
            enc.roundkey[r] = temp[r];
            dec.roundkey[ROUNDS - r] = temp[r];
        }
        for(r = 1; r < ROUNDS; r++)
            diff.transform(dec.roundkey[r]);
    }
}

map<char, string> VocabularyFormation(byte key[] = (byte*)"AAAAAAAAAAAAAAA") {
    ofstream file(FILENAMEVOCUBALARY);
    map<char, string> dictionarySymbol;
    if(!file.is_open()) {
        cout << "Can`t create file vocubalary!" << endl;
        dictionarySymbol.empty();
        return dictionarySymbol;
    }
    file << "KEY: " << key << endl;
    unsigned i;
    setlocale(0, "");
    shark* sk = new shark(key, 16);
    ddword q;
    q.w[0] = 0;
    q.w[1] = 0;
    string encrypttext;
    for(i = 0; i < 258; i++) {
        ddword p;
        p.w[0] = i;
        p.w[1] = 0;

        string encryptText = "", decryptionText = "";
        q = sk->encryption(p);
        cout << "Encrypt: " << q.b[0] << q.b[1] << q.b[2] << q.b[3] << q.b[4] << q.b[5] << q.b[6] << q.b[7] << endl;
        file << "Encrypt: " << q.b[0] << q.b[1] << q.b[2] << q.b[3] << q.b[4] << q.b[5] << q.b[6] << q.b[7] << endl;
        for(int i = 0; i < 8; i++) {
            if (q.b[i] == '\0' || q.b[i] == '\n') {
                encryptText += ' ';
                continue;
            }
            encryptText += q.b[i];
        }
        ddword d = sk->decryption(q);
        cout << "Decryption: " << d.b[0] << d.b[1] << d.b[2] << d.b[3] << d.b[4] << d.b[5] << d.b[6] << d.b[7] << endl;
        file << "Decryption: " << d.b[0] << d.b[1] << d.b[2] << d.b[3] << d.b[4] << d.b[5] << d.b[6] << d.b[7] << endl;
        dictionarySymbol.insert({ d.b[0], encryptText });

        while(d.w[0] != p.w[0]);
        while(d.w[1] != p.w[1]);
     }
    file.close();
    delete sk;
    return dictionarySymbol;
}

string encryptText(map<char, string> dictionary, string text = "TEXT FOR EXAMPLE") {
    ofstream file(FILENAMEENCRYPT);
    if(!file.is_open() || text == "" ) {
        cout << "Can`t create file vocubalary!" << endl;
        dictionary.empty();
        return "";
    }
    text = ReadFileForEncrypt();
    string ciphertext = "";
    int lengthText = text.length();
    for(int i = 0; i < lengthText; i++) {
        auto value = dictionary.find(text[i]);
        ciphertext += value->second;
        file << value->second;
        //cout << ciphertext << endl;
    }
    file.close();
    return ciphertext;
}

string decryptionText(map<char, string> dictionary, string ciphertext = "FJ}YПcхл") {//эм(л)
    if(ciphertext == "") {
        ciphertext = "FJ}YПcхл";
    }
    int lengthText = ciphertext.length();
    if(lengthText % 8 != 0) {
        cout << "Error!" << endl;
        return "Error";
    }
    string decryption = "", eightWord ="";
    for(int i = 0; i < lengthText; i++) {
        eightWord += ciphertext[i];
        if((i + 1) % 8 == 0) {
            for(auto& item : dictionary) {
                if(item.second == eightWord) {
                    decryption += item.first;
                    break;
                }
            }
            eightWord = "";
        }
    }
    cout << ciphertext;
    return decryption;
}

string ReadFileForEncrypt() {
    ifstream file(filenameforencrypt);
    if(!file.is_open()) {
        cout << "Error! File is not exist!" << endl;
        return "";
    }
    string temp = "", str = "";
    while(!file.eof()) {
        file >> temp;
        str += temp;
    }
    file.close();
    return str;
}

bool WriteFile(string filename, string data) {
    ofstream file(filename);
    file.open(filename);
    if(file.is_open()) {
        cout << "Error! File can`t be open!" << endl;
        return false;
    }
    file << data;
    file.close();
    return true;
}

extern "C" int main() {
    byte key[16] = "AAAAAAAAAAAAAAA";
    map<char, string> dictionary = VocabularyFormation(key);
    string str;
    while(true) {
        int choice;
        string choiceStr;
        cout << "1.\tEnter key " << endl;
        cout << "2.\tEncrypt value " << endl;
        cout << "3.\tDecrypt value " << endl;
        cout << "4.\tExit " << endl;
        cout << "  \tEnter value:\t";
        try {
            getline(cin, choiceStr);
            choice = stoi(choiceStr);
            switch (choice) {
            case 1:
                char key[LENGTHKEY];
                cout << "Enter key: ";
                cin.clear();
                cin >> key;
                dictionary = VocabularyFormation((byte*)key);
                break;
            case 2:
                cout << endl << encryptText(dictionary) << endl;
                break;
            case 3:
                str = "";
                cout << "Enter text: ";
                cin.clear();
                getline(cin, str);
                cout << endl << decryptionText(dictionary, str) << endl;
                break;
            case 4:
                exit(-1);
                break;
            default:
                cout << "\nIncorrected value\n";
                break;
            }
        }
        catch(std::invalid_argument e) {
            cout << endl << "ERROR\nIncorrected value!" << endl;
        }
    }
    return 0;
}
