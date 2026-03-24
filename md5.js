/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */
/* MD5 (RFC 1321) implementation in JavaScript                                                     */
/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

/**
 * MD5 hash function reference implementation.
 *
 * This is an annotated direct implementation of RFC 1321, without any optimisations. It is
 * intended to aid understanding of the algorithm rather than for production use.
 *
 * While it could be used where performance is not critical, I would recommend using the ‘Web
 * Cryptography API’ (developer.mozilla.org/en-US/docs/Web/API/SubtleCrypto/digest) for the browser,
 * or the ‘crypto’ library (nodejs.org/api/crypto.html#crypto_class_hash) in Node.js.
 *
 * See datatracker.ietf.org/doc/html/rfc1321
 */
class Md5 {
    /**
     * Generates MD5 hash of string.
     *
     * @param {string} msg - (Unicode) string to be hashed.
     * @param {Object} [options]
     * @param {string} [options.msgFormat=string] - Message format: 'string' for JavaScript string
     * (gets converted to UTF-8 for hashing); 'hex-bytes' for string of hex bytes ('616263' ≡ 'abc') .
     * @param {string} [options.outFormat=hex] - Output format: 'hex' for string of contiguous
     * hex bytes; 'hex-w' for grouping hex bytes into groups of (4 byte / 8 character) words.
     * @returns {string} Hash of msg as hex character string.
     *
     * @example
     * import Md5 from './md5.js';
     * const hash = Md5.hash('abc'); // '900150983cd24fb0d6963f7d28e17f72'
     */
    static hash(msg, options) {
        const defaults = { msgFormat: 'string', outFormat: 'hex' };
        const opt = Object.assign(defaults, options);

        switch (opt.msgFormat) {
            default: // default is to convert string to UTF-8, as MD5 only deals with byte-streams
            case 'string': msg = utf8Encode(msg); break;
            case 'hex-bytes':msg = hexBytesToString(msg); break; // mostly for running tests
        }

        // constants [RFC 1321 §3.4] - T[i] = floor(4294967296 * abs(sin(i)))
        const K = [
            0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
            0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
            0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
            0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
            0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
            0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
            0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
            0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391
        ];

        // shift amounts for each operation
        const S = [
            7, 12, 17, 22,  7, 12, 17, 22,  7, 12, 17, 22,  7, 12, 17, 22,
            5,  9, 14, 20,  5,  9, 14, 20,  5,  9, 14, 20,  5,  9, 14, 20,
            4, 11, 16, 23,  4, 11, 16, 23,  4, 11, 16, 23,  4, 11, 16, 23,
            6, 10, 15, 21,  6, 10, 15, 21,  6, 10, 15, 21,  6, 10, 15, 21
        ];

        // initial hash value [RFC 1321 §3.3]
        const H = [ 0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476 ];

        // PREPROCESSING [RFC 1321 §3.1 & §3.2]
        msg += String.fromCharCode(0x80); // add trailing '1' bit (+ 0's padding) to string

        // convert string msg into 512-bit/16-integer blocks arrays of ints
        const l = msg.length/4 + 2; // length (in 32-bit integers) of msg + ‘1’ + appended length
        const N = Math.ceil(l/16); // number of 16-integer-blocks required to hold 'l' ints
        const M = new Array(N);

        for (let i=0; i<N; i++) {
            M[i] = new Array(16);
            for (let j=0; j<16; j++) { // encode 4 chars per integer, little-endian encoding (different from SHA-1)
                M[i][j] = (msg.charCodeAt(i*64+j*4+0)<< 0) | (msg.charCodeAt(i*64+j*4+1)<< 8)
                        | (msg.charCodeAt(i*64+j*4+2)<<16) | (msg.charCodeAt(i*64+j*4+3)<<24);
            } // note running off the end of msg is ok 'cos bitwise ops on NaN return 0
        }

        // add length (in bits) into final pair of 32-bit integers (little-endian)
        M[N-1][14] = ((msg.length-1)*8) & 0xffffffff;
        M[N-1][15] = Math.floor(((msg.length-1)*8) / Math.pow(2, 32));

        // HASH COMPUTATION [RFC 1321 §3.4]
        for (let i=0; i<N; i++) {
            // initialise four working variables a, b, c, d with previous hash value
            let a = H[0], b = H[1], c = H[2], d = H[3];

            // main loop (use JavaScript '>>> 0' to emulate UInt32 variables)
            for (let t=0; t<64; t++) {
                let f, g;
                if (t < 16) {
                    f = (b & c) | ((~b) & d);
                    g = t;
                } else if (t < 32) {
                    f = (d & b) | ((~d) & c);
                    g = (5*t + 1) % 16;
                } else if (t < 48) {
                    f = b ^ c ^ d;
                    g = (3*t + 5) % 16;
                } else {
                    f = c ^ (b | (~d));
                    g = (7*t) % 16;
                }

                const temp = d;
                d = c;
                c = b;
                b = (b + Md5.ROTL((a + f + K[t] + M[i][g]) >>> 0, S[t])) >>> 0;
                a = temp;
            }

            // compute the new intermediate hash value
            H[0] = (H[0]+a) >>> 0;
            H[1] = (H[1]+b) >>> 0;
            H[2] = (H[2]+c) >>> 0;
            H[3] = (H[3]+d) >>> 0;
        }

        // convert H0..H3 to hex strings (little-endian output required by MD5)
        for (let h=0; h<H.length; h++) {
            const bytes = [
                (H[h] >>>  0) & 0xff,
                (H[h] >>>  8) & 0xff,
                (H[h] >>> 16) & 0xff,
                (H[h] >>> 24) & 0xff
            ];
            H[h] = bytes.map(b => ('00' + b.toString(16)).slice(-2)).join('');
        }

        // concatenate H0..H3, with separator if required
        const separator = opt.outFormat=='hex-w' ? ' ' : '';
        return H.join(separator);

        /* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

        function utf8Encode(str) {
            try {
                return new TextEncoder().encode(str, 'utf-8').reduce((prev, curr) => prev + String.fromCharCode(curr), '');
            } catch (e) { // no TextEncoder available?
                return unescape(encodeURIComponent(str)); // monsur.hossa.in/2012/07/20/utf-8-in-javascript.html
            }
        }

        function hexBytesToString(hexStr) { // convert string of hex numbers to a string of chars (eg '616263' -> 'abc').
            const str = hexStr.replace(/ /g, ''); // allow space-separated groups
            return str=='' ? '' : str.match(/.{2}/g).map(byte => String.fromCharCode(parseInt(byte, 16))).join('');
        }
    }

    /**
     * Rotates left (circular left shift) value x by n positions.
     * @private
     */
    static ROTL(x, n) {
        return (x<<n) | (x>>>(32-n));
    }
}

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

export default Md5;
