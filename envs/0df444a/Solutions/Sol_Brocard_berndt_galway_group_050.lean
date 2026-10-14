-- Prove2me | solution 1 for Brocard.berndt_galway_group_050
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:26:37.292995+00:00
-- url     : https://prove2.me/submissions/9453f57f-2794-490a-839f-f83c6e325e52

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_2272
import Theorems.Thm_Brocard_berndt_galway_chunk_2273
import Theorems.Thm_Brocard_berndt_galway_chunk_2274
import Theorems.Thm_Brocard_berndt_galway_chunk_2275
import Theorems.Thm_Brocard_berndt_galway_chunk_2276
import Theorems.Thm_Brocard_berndt_galway_chunk_2277
import Theorems.Thm_Brocard_berndt_galway_chunk_2278
import Theorems.Thm_Brocard_berndt_galway_chunk_2279
import Theorems.Thm_Brocard_berndt_galway_chunk_2280
import Theorems.Thm_Brocard_berndt_galway_chunk_2281
import Theorems.Thm_Brocard_berndt_galway_chunk_2282
import Theorems.Thm_Brocard_berndt_galway_chunk_2283
import Theorems.Thm_Brocard_berndt_galway_chunk_2284
import Theorems.Thm_Brocard_berndt_galway_chunk_2285
import Theorems.Thm_Brocard_berndt_galway_chunk_2286
import Theorems.Thm_Brocard_berndt_galway_chunk_2287
import Theorems.Thm_Brocard_berndt_galway_chunk_2288
import Theorems.Thm_Brocard_berndt_galway_chunk_2289
import Theorems.Thm_Brocard_berndt_galway_chunk_2290
import Theorems.Thm_Brocard_berndt_galway_chunk_2291
import Theorems.Thm_Brocard_berndt_galway_chunk_2292
import Theorems.Thm_Brocard_berndt_galway_chunk_2293
import Theorems.Thm_Brocard_berndt_galway_chunk_2294
import Theorems.Thm_Brocard_berndt_galway_chunk_2295
import Theorems.Thm_Brocard_berndt_galway_chunk_2296
import Theorems.Thm_Brocard_berndt_galway_chunk_2297
import Theorems.Thm_Brocard_berndt_galway_chunk_2298
import Theorems.Thm_Brocard_berndt_galway_chunk_2299
import Theorems.Thm_Brocard_berndt_galway_chunk_2300
import Theorems.Thm_Brocard_berndt_galway_chunk_2301
import Theorems.Thm_Brocard_berndt_galway_chunk_2302
import Theorems.Thm_Brocard_berndt_galway_chunk_2303
import Theorems.Thm_Brocard_berndt_galway_chunk_2304
import Theorems.Thm_Brocard_berndt_galway_chunk_2305
import Theorems.Thm_Brocard_berndt_galway_chunk_2306
import Theorems.Thm_Brocard_berndt_galway_chunk_2307
import Theorems.Thm_Brocard_berndt_galway_chunk_2308
import Theorems.Thm_Brocard_berndt_galway_chunk_2309
import Theorems.Thm_Brocard_berndt_galway_chunk_2310
import Theorems.Thm_Brocard_berndt_galway_chunk_2311
import Theorems.Thm_Brocard_berndt_galway_chunk_2312
import Theorems.Thm_Brocard_berndt_galway_chunk_2313
import Theorems.Thm_Brocard_berndt_galway_chunk_2314
import Theorems.Thm_Brocard_berndt_galway_chunk_2315
import Theorems.Thm_Brocard_berndt_galway_chunk_2316
import Theorems.Thm_Brocard_berndt_galway_chunk_2317
import Theorems.Thm_Brocard_berndt_galway_chunk_2318

theorem solution (n m : ℕ) (h1 : 408453237 ≤ n) (h2 : n < 416906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 412769784 with hs0 | hs0
  · -- n < 412769784
    rcases Nat.lt_or_ge n 410611510 with hs1 | hs1
    · -- n < 410611510
      rcases Nat.lt_or_ge n 409532374 with hs2 | hs2
      · -- n < 409532374
        rcases Nat.lt_or_ge n 408992805 with hs3 | hs3
        · -- n < 408992805
          rcases Nat.lt_or_ge n 408812949 with hs4 | hs4
          · -- n < 408812949
            rcases Nat.lt_or_ge n 408633093 with hs5 | hs5
            · -- n < 408633093
              exact Brocard.berndt_galway_chunk_2272 n m (by omega) (by omega) h
            · -- n >= 408633093
              exact Brocard.berndt_galway_chunk_2273 n m (by omega) (by omega) h
          · -- n >= 408812949
            exact Brocard.berndt_galway_chunk_2274 n m (by omega) (by omega) h
        · -- n >= 408992805
          rcases Nat.lt_or_ge n 409352517 with hs4 | hs4
          · -- n < 409352517
            rcases Nat.lt_or_ge n 409172661 with hs5 | hs5
            · -- n < 409172661
              exact Brocard.berndt_galway_chunk_2275 n m (by omega) (by omega) h
            · -- n >= 409172661
              exact Brocard.berndt_galway_chunk_2276 n m (by omega) (by omega) h
          · -- n >= 409352517
            exact Brocard.berndt_galway_chunk_2277 n m (by omega) (by omega) h
      · -- n >= 409532374
        rcases Nat.lt_or_ge n 410071942 with hs3 | hs3
        · -- n < 410071942
          rcases Nat.lt_or_ge n 409892086 with hs4 | hs4
          · -- n < 409892086
            rcases Nat.lt_or_ge n 409712230 with hs5 | hs5
            · -- n < 409712230
              exact Brocard.berndt_galway_chunk_2278 n m (by omega) (by omega) h
            · -- n >= 409712230
              exact Brocard.berndt_galway_chunk_2279 n m (by omega) (by omega) h
          · -- n >= 409892086
            exact Brocard.berndt_galway_chunk_2280 n m (by omega) (by omega) h
        · -- n >= 410071942
          rcases Nat.lt_or_ge n 410431654 with hs4 | hs4
          · -- n < 410431654
            rcases Nat.lt_or_ge n 410251798 with hs5 | hs5
            · -- n < 410251798
              exact Brocard.berndt_galway_chunk_2281 n m (by omega) (by omega) h
            · -- n >= 410251798
              exact Brocard.berndt_galway_chunk_2282 n m (by omega) (by omega) h
          · -- n >= 410431654
            exact Brocard.berndt_galway_chunk_2283 n m (by omega) (by omega) h
    · -- n >= 410611510
      rcases Nat.lt_or_ge n 411690647 with hs2 | hs2
      · -- n < 411690647
        rcases Nat.lt_or_ge n 411151079 with hs3 | hs3
        · -- n < 411151079
          rcases Nat.lt_or_ge n 410971223 with hs4 | hs4
          · -- n < 410971223
            rcases Nat.lt_or_ge n 410791366 with hs5 | hs5
            · -- n < 410791366
              exact Brocard.berndt_galway_chunk_2284 n m (by omega) (by omega) h
            · -- n >= 410791366
              exact Brocard.berndt_galway_chunk_2285 n m (by omega) (by omega) h
          · -- n >= 410971223
            exact Brocard.berndt_galway_chunk_2286 n m (by omega) (by omega) h
        · -- n >= 411151079
          rcases Nat.lt_or_ge n 411510791 with hs4 | hs4
          · -- n < 411510791
            rcases Nat.lt_or_ge n 411330935 with hs5 | hs5
            · -- n < 411330935
              exact Brocard.berndt_galway_chunk_2287 n m (by omega) (by omega) h
            · -- n >= 411330935
              exact Brocard.berndt_galway_chunk_2288 n m (by omega) (by omega) h
          · -- n >= 411510791
            exact Brocard.berndt_galway_chunk_2289 n m (by omega) (by omega) h
      · -- n >= 411690647
        rcases Nat.lt_or_ge n 412230215 with hs3 | hs3
        · -- n < 412230215
          rcases Nat.lt_or_ge n 412050359 with hs4 | hs4
          · -- n < 412050359
            rcases Nat.lt_or_ge n 411870503 with hs5 | hs5
            · -- n < 411870503
              exact Brocard.berndt_galway_chunk_2290 n m (by omega) (by omega) h
            · -- n >= 411870503
              exact Brocard.berndt_galway_chunk_2291 n m (by omega) (by omega) h
          · -- n >= 412050359
            exact Brocard.berndt_galway_chunk_2292 n m (by omega) (by omega) h
        · -- n >= 412230215
          rcases Nat.lt_or_ge n 412589928 with hs4 | hs4
          · -- n < 412589928
            rcases Nat.lt_or_ge n 412410071 with hs5 | hs5
            · -- n < 412410071
              exact Brocard.berndt_galway_chunk_2293 n m (by omega) (by omega) h
            · -- n >= 412410071
              exact Brocard.berndt_galway_chunk_2294 n m (by omega) (by omega) h
          · -- n >= 412589928
            exact Brocard.berndt_galway_chunk_2295 n m (by omega) (by omega) h
  · -- n >= 412769784
    rcases Nat.lt_or_ge n 414928057 with hs1 | hs1
    · -- n < 414928057
      rcases Nat.lt_or_ge n 413848920 with hs2 | hs2
      · -- n < 413848920
        rcases Nat.lt_or_ge n 413309352 with hs3 | hs3
        · -- n < 413309352
          rcases Nat.lt_or_ge n 413129496 with hs4 | hs4
          · -- n < 413129496
            rcases Nat.lt_or_ge n 412949640 with hs5 | hs5
            · -- n < 412949640
              exact Brocard.berndt_galway_chunk_2296 n m (by omega) (by omega) h
            · -- n >= 412949640
              exact Brocard.berndt_galway_chunk_2297 n m (by omega) (by omega) h
          · -- n >= 413129496
            exact Brocard.berndt_galway_chunk_2298 n m (by omega) (by omega) h
        · -- n >= 413309352
          rcases Nat.lt_or_ge n 413669064 with hs4 | hs4
          · -- n < 413669064
            rcases Nat.lt_or_ge n 413489208 with hs5 | hs5
            · -- n < 413489208
              exact Brocard.berndt_galway_chunk_2299 n m (by omega) (by omega) h
            · -- n >= 413489208
              exact Brocard.berndt_galway_chunk_2300 n m (by omega) (by omega) h
          · -- n >= 413669064
            exact Brocard.berndt_galway_chunk_2301 n m (by omega) (by omega) h
      · -- n >= 413848920
        rcases Nat.lt_or_ge n 414388489 with hs3 | hs3
        · -- n < 414388489
          rcases Nat.lt_or_ge n 414208633 with hs4 | hs4
          · -- n < 414208633
            rcases Nat.lt_or_ge n 414028776 with hs5 | hs5
            · -- n < 414028776
              exact Brocard.berndt_galway_chunk_2302 n m (by omega) (by omega) h
            · -- n >= 414028776
              exact Brocard.berndt_galway_chunk_2303 n m (by omega) (by omega) h
          · -- n >= 414208633
            exact Brocard.berndt_galway_chunk_2304 n m (by omega) (by omega) h
        · -- n >= 414388489
          rcases Nat.lt_or_ge n 414748201 with hs4 | hs4
          · -- n < 414748201
            rcases Nat.lt_or_ge n 414568345 with hs5 | hs5
            · -- n < 414568345
              exact Brocard.berndt_galway_chunk_2305 n m (by omega) (by omega) h
            · -- n >= 414568345
              exact Brocard.berndt_galway_chunk_2306 n m (by omega) (by omega) h
          · -- n >= 414748201
            exact Brocard.berndt_galway_chunk_2307 n m (by omega) (by omega) h
    · -- n >= 414928057
      rcases Nat.lt_or_ge n 416007194 with hs2 | hs2
      · -- n < 416007194
        rcases Nat.lt_or_ge n 415467625 with hs3 | hs3
        · -- n < 415467625
          rcases Nat.lt_or_ge n 415287769 with hs4 | hs4
          · -- n < 415287769
            rcases Nat.lt_or_ge n 415107913 with hs5 | hs5
            · -- n < 415107913
              exact Brocard.berndt_galway_chunk_2308 n m (by omega) (by omega) h
            · -- n >= 415107913
              exact Brocard.berndt_galway_chunk_2309 n m (by omega) (by omega) h
          · -- n >= 415287769
            exact Brocard.berndt_galway_chunk_2310 n m (by omega) (by omega) h
        · -- n >= 415467625
          rcases Nat.lt_or_ge n 415827338 with hs4 | hs4
          · -- n < 415827338
            rcases Nat.lt_or_ge n 415647482 with hs5 | hs5
            · -- n < 415647482
              exact Brocard.berndt_galway_chunk_2311 n m (by omega) (by omega) h
            · -- n >= 415647482
              exact Brocard.berndt_galway_chunk_2312 n m (by omega) (by omega) h
          · -- n >= 415827338
            exact Brocard.berndt_galway_chunk_2313 n m (by omega) (by omega) h
      · -- n >= 416007194
        rcases Nat.lt_or_ge n 416546762 with hs3 | hs3
        · -- n < 416546762
          rcases Nat.lt_or_ge n 416366906 with hs4 | hs4
          · -- n < 416366906
            rcases Nat.lt_or_ge n 416187050 with hs5 | hs5
            · -- n < 416187050
              exact Brocard.berndt_galway_chunk_2314 n m (by omega) (by omega) h
            · -- n >= 416187050
              exact Brocard.berndt_galway_chunk_2315 n m (by omega) (by omega) h
          · -- n >= 416366906
            exact Brocard.berndt_galway_chunk_2316 n m (by omega) (by omega) h
        · -- n >= 416546762
          rcases Nat.lt_or_ge n 416726618 with hs4 | hs4
          · -- n < 416726618
            exact Brocard.berndt_galway_chunk_2317 n m (by omega) (by omega) h
          · -- n >= 416726618
            exact Brocard.berndt_galway_chunk_2318 n m (by omega) (by omega) h
