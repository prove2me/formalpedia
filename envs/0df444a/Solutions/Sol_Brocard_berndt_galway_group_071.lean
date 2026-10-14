-- Prove2me | solution 1 for Brocard.berndt_galway_group_071
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:21:19.495716+00:00
-- url     : https://prove2.me/submissions/92a877d7-fc4a-4fa1-8702-03b35deddfd6

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_3245
import Theorems.Thm_Brocard_berndt_galway_chunk_3246
import Theorems.Thm_Brocard_berndt_galway_chunk_3247
import Theorems.Thm_Brocard_berndt_galway_chunk_3248
import Theorems.Thm_Brocard_berndt_galway_chunk_3249
import Theorems.Thm_Brocard_berndt_galway_chunk_3250
import Theorems.Thm_Brocard_berndt_galway_chunk_3251
import Theorems.Thm_Brocard_berndt_galway_chunk_3252
import Theorems.Thm_Brocard_berndt_galway_chunk_3253
import Theorems.Thm_Brocard_berndt_galway_chunk_3254
import Theorems.Thm_Brocard_berndt_galway_chunk_3255
import Theorems.Thm_Brocard_berndt_galway_chunk_3256
import Theorems.Thm_Brocard_berndt_galway_chunk_3257
import Theorems.Thm_Brocard_berndt_galway_chunk_3258
import Theorems.Thm_Brocard_berndt_galway_chunk_3259
import Theorems.Thm_Brocard_berndt_galway_chunk_3260
import Theorems.Thm_Brocard_berndt_galway_chunk_3261
import Theorems.Thm_Brocard_berndt_galway_chunk_3262
import Theorems.Thm_Brocard_berndt_galway_chunk_3263
import Theorems.Thm_Brocard_berndt_galway_chunk_3264
import Theorems.Thm_Brocard_berndt_galway_chunk_3265
import Theorems.Thm_Brocard_berndt_galway_chunk_3266
import Theorems.Thm_Brocard_berndt_galway_chunk_3267
import Theorems.Thm_Brocard_berndt_galway_chunk_3268
import Theorems.Thm_Brocard_berndt_galway_chunk_3269
import Theorems.Thm_Brocard_berndt_galway_chunk_3270
import Theorems.Thm_Brocard_berndt_galway_chunk_3271
import Theorems.Thm_Brocard_berndt_galway_chunk_3272
import Theorems.Thm_Brocard_berndt_galway_chunk_3273
import Theorems.Thm_Brocard_berndt_galway_chunk_3274
import Theorems.Thm_Brocard_berndt_galway_chunk_3275
import Theorems.Thm_Brocard_berndt_galway_chunk_3276
import Theorems.Thm_Brocard_berndt_galway_chunk_3277
import Theorems.Thm_Brocard_berndt_galway_chunk_3278
import Theorems.Thm_Brocard_berndt_galway_chunk_3279
import Theorems.Thm_Brocard_berndt_galway_chunk_3280
import Theorems.Thm_Brocard_berndt_galway_chunk_3281
import Theorems.Thm_Brocard_berndt_galway_chunk_3282
import Theorems.Thm_Brocard_berndt_galway_chunk_3283
import Theorems.Thm_Brocard_berndt_galway_chunk_3284
import Theorems.Thm_Brocard_berndt_galway_chunk_3285
import Theorems.Thm_Brocard_berndt_galway_chunk_3286
import Theorems.Thm_Brocard_berndt_galway_chunk_3287
import Theorems.Thm_Brocard_berndt_galway_chunk_3288
import Theorems.Thm_Brocard_berndt_galway_chunk_3289
import Theorems.Thm_Brocard_berndt_galway_chunk_3290

theorem solution (n m : ℕ) (h1 : 583453237 ≤ n) (h2 : n < 591726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 587589928 with hs0 | hs0
  · -- n < 587589928
    rcases Nat.lt_or_ge n 585611510 with hs1 | hs1
    · -- n < 585611510
      rcases Nat.lt_or_ge n 584532374 with hs2 | hs2
      · -- n < 584532374
        rcases Nat.lt_or_ge n 583992805 with hs3 | hs3
        · -- n < 583992805
          rcases Nat.lt_or_ge n 583812949 with hs4 | hs4
          · -- n < 583812949
            rcases Nat.lt_or_ge n 583633093 with hs5 | hs5
            · -- n < 583633093
              exact Brocard.berndt_galway_chunk_3245 n m (by omega) (by omega) h
            · -- n >= 583633093
              exact Brocard.berndt_galway_chunk_3246 n m (by omega) (by omega) h
          · -- n >= 583812949
            exact Brocard.berndt_galway_chunk_3247 n m (by omega) (by omega) h
        · -- n >= 583992805
          rcases Nat.lt_or_ge n 584352517 with hs4 | hs4
          · -- n < 584352517
            rcases Nat.lt_or_ge n 584172661 with hs5 | hs5
            · -- n < 584172661
              exact Brocard.berndt_galway_chunk_3248 n m (by omega) (by omega) h
            · -- n >= 584172661
              exact Brocard.berndt_galway_chunk_3249 n m (by omega) (by omega) h
          · -- n >= 584352517
            exact Brocard.berndt_galway_chunk_3250 n m (by omega) (by omega) h
      · -- n >= 584532374
        rcases Nat.lt_or_ge n 585071942 with hs3 | hs3
        · -- n < 585071942
          rcases Nat.lt_or_ge n 584892086 with hs4 | hs4
          · -- n < 584892086
            rcases Nat.lt_or_ge n 584712230 with hs5 | hs5
            · -- n < 584712230
              exact Brocard.berndt_galway_chunk_3251 n m (by omega) (by omega) h
            · -- n >= 584712230
              exact Brocard.berndt_galway_chunk_3252 n m (by omega) (by omega) h
          · -- n >= 584892086
            exact Brocard.berndt_galway_chunk_3253 n m (by omega) (by omega) h
        · -- n >= 585071942
          rcases Nat.lt_or_ge n 585431654 with hs4 | hs4
          · -- n < 585431654
            rcases Nat.lt_or_ge n 585251798 with hs5 | hs5
            · -- n < 585251798
              exact Brocard.berndt_galway_chunk_3254 n m (by omega) (by omega) h
            · -- n >= 585251798
              exact Brocard.berndt_galway_chunk_3255 n m (by omega) (by omega) h
          · -- n >= 585431654
            exact Brocard.berndt_galway_chunk_3256 n m (by omega) (by omega) h
    · -- n >= 585611510
      rcases Nat.lt_or_ge n 586690647 with hs2 | hs2
      · -- n < 586690647
        rcases Nat.lt_or_ge n 586151079 with hs3 | hs3
        · -- n < 586151079
          rcases Nat.lt_or_ge n 585971223 with hs4 | hs4
          · -- n < 585971223
            rcases Nat.lt_or_ge n 585791366 with hs5 | hs5
            · -- n < 585791366
              exact Brocard.berndt_galway_chunk_3257 n m (by omega) (by omega) h
            · -- n >= 585791366
              exact Brocard.berndt_galway_chunk_3258 n m (by omega) (by omega) h
          · -- n >= 585971223
            exact Brocard.berndt_galway_chunk_3259 n m (by omega) (by omega) h
        · -- n >= 586151079
          rcases Nat.lt_or_ge n 586510791 with hs4 | hs4
          · -- n < 586510791
            rcases Nat.lt_or_ge n 586330935 with hs5 | hs5
            · -- n < 586330935
              exact Brocard.berndt_galway_chunk_3260 n m (by omega) (by omega) h
            · -- n >= 586330935
              exact Brocard.berndt_galway_chunk_3261 n m (by omega) (by omega) h
          · -- n >= 586510791
            exact Brocard.berndt_galway_chunk_3262 n m (by omega) (by omega) h
      · -- n >= 586690647
        rcases Nat.lt_or_ge n 587230215 with hs3 | hs3
        · -- n < 587230215
          rcases Nat.lt_or_ge n 587050359 with hs4 | hs4
          · -- n < 587050359
            rcases Nat.lt_or_ge n 586870503 with hs5 | hs5
            · -- n < 586870503
              exact Brocard.berndt_galway_chunk_3263 n m (by omega) (by omega) h
            · -- n >= 586870503
              exact Brocard.berndt_galway_chunk_3264 n m (by omega) (by omega) h
          · -- n >= 587050359
            exact Brocard.berndt_galway_chunk_3265 n m (by omega) (by omega) h
        · -- n >= 587230215
          rcases Nat.lt_or_ge n 587410071 with hs4 | hs4
          · -- n < 587410071
            exact Brocard.berndt_galway_chunk_3266 n m (by omega) (by omega) h
          · -- n >= 587410071
            exact Brocard.berndt_galway_chunk_3267 n m (by omega) (by omega) h
  · -- n >= 587589928
    rcases Nat.lt_or_ge n 589748201 with hs1 | hs1
    · -- n < 589748201
      rcases Nat.lt_or_ge n 588669064 with hs2 | hs2
      · -- n < 588669064
        rcases Nat.lt_or_ge n 588129496 with hs3 | hs3
        · -- n < 588129496
          rcases Nat.lt_or_ge n 587949640 with hs4 | hs4
          · -- n < 587949640
            rcases Nat.lt_or_ge n 587769784 with hs5 | hs5
            · -- n < 587769784
              exact Brocard.berndt_galway_chunk_3268 n m (by omega) (by omega) h
            · -- n >= 587769784
              exact Brocard.berndt_galway_chunk_3269 n m (by omega) (by omega) h
          · -- n >= 587949640
            exact Brocard.berndt_galway_chunk_3270 n m (by omega) (by omega) h
        · -- n >= 588129496
          rcases Nat.lt_or_ge n 588489208 with hs4 | hs4
          · -- n < 588489208
            rcases Nat.lt_or_ge n 588309352 with hs5 | hs5
            · -- n < 588309352
              exact Brocard.berndt_galway_chunk_3271 n m (by omega) (by omega) h
            · -- n >= 588309352
              exact Brocard.berndt_galway_chunk_3272 n m (by omega) (by omega) h
          · -- n >= 588489208
            exact Brocard.berndt_galway_chunk_3273 n m (by omega) (by omega) h
      · -- n >= 588669064
        rcases Nat.lt_or_ge n 589208633 with hs3 | hs3
        · -- n < 589208633
          rcases Nat.lt_or_ge n 589028776 with hs4 | hs4
          · -- n < 589028776
            rcases Nat.lt_or_ge n 588848920 with hs5 | hs5
            · -- n < 588848920
              exact Brocard.berndt_galway_chunk_3274 n m (by omega) (by omega) h
            · -- n >= 588848920
              exact Brocard.berndt_galway_chunk_3275 n m (by omega) (by omega) h
          · -- n >= 589028776
            exact Brocard.berndt_galway_chunk_3276 n m (by omega) (by omega) h
        · -- n >= 589208633
          rcases Nat.lt_or_ge n 589568345 with hs4 | hs4
          · -- n < 589568345
            rcases Nat.lt_or_ge n 589388489 with hs5 | hs5
            · -- n < 589388489
              exact Brocard.berndt_galway_chunk_3277 n m (by omega) (by omega) h
            · -- n >= 589388489
              exact Brocard.berndt_galway_chunk_3278 n m (by omega) (by omega) h
          · -- n >= 589568345
            exact Brocard.berndt_galway_chunk_3279 n m (by omega) (by omega) h
    · -- n >= 589748201
      rcases Nat.lt_or_ge n 590827338 with hs2 | hs2
      · -- n < 590827338
        rcases Nat.lt_or_ge n 590287769 with hs3 | hs3
        · -- n < 590287769
          rcases Nat.lt_or_ge n 590107913 with hs4 | hs4
          · -- n < 590107913
            rcases Nat.lt_or_ge n 589928057 with hs5 | hs5
            · -- n < 589928057
              exact Brocard.berndt_galway_chunk_3280 n m (by omega) (by omega) h
            · -- n >= 589928057
              exact Brocard.berndt_galway_chunk_3281 n m (by omega) (by omega) h
          · -- n >= 590107913
            exact Brocard.berndt_galway_chunk_3282 n m (by omega) (by omega) h
        · -- n >= 590287769
          rcases Nat.lt_or_ge n 590647482 with hs4 | hs4
          · -- n < 590647482
            rcases Nat.lt_or_ge n 590467625 with hs5 | hs5
            · -- n < 590467625
              exact Brocard.berndt_galway_chunk_3283 n m (by omega) (by omega) h
            · -- n >= 590467625
              exact Brocard.berndt_galway_chunk_3284 n m (by omega) (by omega) h
          · -- n >= 590647482
            exact Brocard.berndt_galway_chunk_3285 n m (by omega) (by omega) h
      · -- n >= 590827338
        rcases Nat.lt_or_ge n 591366906 with hs3 | hs3
        · -- n < 591366906
          rcases Nat.lt_or_ge n 591187050 with hs4 | hs4
          · -- n < 591187050
            rcases Nat.lt_or_ge n 591007194 with hs5 | hs5
            · -- n < 591007194
              exact Brocard.berndt_galway_chunk_3286 n m (by omega) (by omega) h
            · -- n >= 591007194
              exact Brocard.berndt_galway_chunk_3287 n m (by omega) (by omega) h
          · -- n >= 591187050
            exact Brocard.berndt_galway_chunk_3288 n m (by omega) (by omega) h
        · -- n >= 591366906
          rcases Nat.lt_or_ge n 591546762 with hs4 | hs4
          · -- n < 591546762
            exact Brocard.berndt_galway_chunk_3289 n m (by omega) (by omega) h
          · -- n >= 591546762
            exact Brocard.berndt_galway_chunk_3290 n m (by omega) (by omega) h
