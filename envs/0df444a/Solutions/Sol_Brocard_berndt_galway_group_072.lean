-- Prove2me | solution 1 for Brocard.berndt_galway_group_072
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:29:39.69257+00:00
-- url     : https://prove2.me/submissions/1df0f022-7dce-49c9-93ab-aefd373f8088

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_3291
import Theorems.Thm_Brocard_berndt_galway_chunk_3292
import Theorems.Thm_Brocard_berndt_galway_chunk_3293
import Theorems.Thm_Brocard_berndt_galway_chunk_3294
import Theorems.Thm_Brocard_berndt_galway_chunk_3295
import Theorems.Thm_Brocard_berndt_galway_chunk_3296
import Theorems.Thm_Brocard_berndt_galway_chunk_3297
import Theorems.Thm_Brocard_berndt_galway_chunk_3298
import Theorems.Thm_Brocard_berndt_galway_chunk_3299
import Theorems.Thm_Brocard_berndt_galway_chunk_3300
import Theorems.Thm_Brocard_berndt_galway_chunk_3301
import Theorems.Thm_Brocard_berndt_galway_chunk_3302
import Theorems.Thm_Brocard_berndt_galway_chunk_3303
import Theorems.Thm_Brocard_berndt_galway_chunk_3304
import Theorems.Thm_Brocard_berndt_galway_chunk_3305
import Theorems.Thm_Brocard_berndt_galway_chunk_3306
import Theorems.Thm_Brocard_berndt_galway_chunk_3307
import Theorems.Thm_Brocard_berndt_galway_chunk_3308
import Theorems.Thm_Brocard_berndt_galway_chunk_3309
import Theorems.Thm_Brocard_berndt_galway_chunk_3310
import Theorems.Thm_Brocard_berndt_galway_chunk_3311
import Theorems.Thm_Brocard_berndt_galway_chunk_3312
import Theorems.Thm_Brocard_berndt_galway_chunk_3313
import Theorems.Thm_Brocard_berndt_galway_chunk_3314
import Theorems.Thm_Brocard_berndt_galway_chunk_3315
import Theorems.Thm_Brocard_berndt_galway_chunk_3316
import Theorems.Thm_Brocard_berndt_galway_chunk_3317
import Theorems.Thm_Brocard_berndt_galway_chunk_3318
import Theorems.Thm_Brocard_berndt_galway_chunk_3319
import Theorems.Thm_Brocard_berndt_galway_chunk_3320
import Theorems.Thm_Brocard_berndt_galway_chunk_3321
import Theorems.Thm_Brocard_berndt_galway_chunk_3322
import Theorems.Thm_Brocard_berndt_galway_chunk_3323
import Theorems.Thm_Brocard_berndt_galway_chunk_3324
import Theorems.Thm_Brocard_berndt_galway_chunk_3325
import Theorems.Thm_Brocard_berndt_galway_chunk_3326
import Theorems.Thm_Brocard_berndt_galway_chunk_3327
import Theorems.Thm_Brocard_berndt_galway_chunk_3328
import Theorems.Thm_Brocard_berndt_galway_chunk_3329
import Theorems.Thm_Brocard_berndt_galway_chunk_3330
import Theorems.Thm_Brocard_berndt_galway_chunk_3331
import Theorems.Thm_Brocard_berndt_galway_chunk_3332
import Theorems.Thm_Brocard_berndt_galway_chunk_3333
import Theorems.Thm_Brocard_berndt_galway_chunk_3334
import Theorems.Thm_Brocard_berndt_galway_chunk_3335
import Theorems.Thm_Brocard_berndt_galway_chunk_3336

theorem solution (n m : ℕ) (h1 : 591726618 ≤ n) (h2 : n < 600000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 595863309 with hs0 | hs0
  · -- n < 595863309
    rcases Nat.lt_or_ge n 593884892 with hs1 | hs1
    · -- n < 593884892
      rcases Nat.lt_or_ge n 592805755 with hs2 | hs2
      · -- n < 592805755
        rcases Nat.lt_or_ge n 592266187 with hs3 | hs3
        · -- n < 592266187
          rcases Nat.lt_or_ge n 592086330 with hs4 | hs4
          · -- n < 592086330
            rcases Nat.lt_or_ge n 591906474 with hs5 | hs5
            · -- n < 591906474
              exact Brocard.berndt_galway_chunk_3291 n m (by omega) (by omega) h
            · -- n >= 591906474
              exact Brocard.berndt_galway_chunk_3292 n m (by omega) (by omega) h
          · -- n >= 592086330
            exact Brocard.berndt_galway_chunk_3293 n m (by omega) (by omega) h
        · -- n >= 592266187
          rcases Nat.lt_or_ge n 592625899 with hs4 | hs4
          · -- n < 592625899
            rcases Nat.lt_or_ge n 592446043 with hs5 | hs5
            · -- n < 592446043
              exact Brocard.berndt_galway_chunk_3294 n m (by omega) (by omega) h
            · -- n >= 592446043
              exact Brocard.berndt_galway_chunk_3295 n m (by omega) (by omega) h
          · -- n >= 592625899
            exact Brocard.berndt_galway_chunk_3296 n m (by omega) (by omega) h
      · -- n >= 592805755
        rcases Nat.lt_or_ge n 593345323 with hs3 | hs3
        · -- n < 593345323
          rcases Nat.lt_or_ge n 593165467 with hs4 | hs4
          · -- n < 593165467
            rcases Nat.lt_or_ge n 592985611 with hs5 | hs5
            · -- n < 592985611
              exact Brocard.berndt_galway_chunk_3297 n m (by omega) (by omega) h
            · -- n >= 592985611
              exact Brocard.berndt_galway_chunk_3298 n m (by omega) (by omega) h
          · -- n >= 593165467
            exact Brocard.berndt_galway_chunk_3299 n m (by omega) (by omega) h
        · -- n >= 593345323
          rcases Nat.lt_or_ge n 593705035 with hs4 | hs4
          · -- n < 593705035
            rcases Nat.lt_or_ge n 593525179 with hs5 | hs5
            · -- n < 593525179
              exact Brocard.berndt_galway_chunk_3300 n m (by omega) (by omega) h
            · -- n >= 593525179
              exact Brocard.berndt_galway_chunk_3301 n m (by omega) (by omega) h
          · -- n >= 593705035
            exact Brocard.berndt_galway_chunk_3302 n m (by omega) (by omega) h
    · -- n >= 593884892
      rcases Nat.lt_or_ge n 594964028 with hs2 | hs2
      · -- n < 594964028
        rcases Nat.lt_or_ge n 594424460 with hs3 | hs3
        · -- n < 594424460
          rcases Nat.lt_or_ge n 594244604 with hs4 | hs4
          · -- n < 594244604
            rcases Nat.lt_or_ge n 594064748 with hs5 | hs5
            · -- n < 594064748
              exact Brocard.berndt_galway_chunk_3303 n m (by omega) (by omega) h
            · -- n >= 594064748
              exact Brocard.berndt_galway_chunk_3304 n m (by omega) (by omega) h
          · -- n >= 594244604
            exact Brocard.berndt_galway_chunk_3305 n m (by omega) (by omega) h
        · -- n >= 594424460
          rcases Nat.lt_or_ge n 594784172 with hs4 | hs4
          · -- n < 594784172
            rcases Nat.lt_or_ge n 594604316 with hs5 | hs5
            · -- n < 594604316
              exact Brocard.berndt_galway_chunk_3306 n m (by omega) (by omega) h
            · -- n >= 594604316
              exact Brocard.berndt_galway_chunk_3307 n m (by omega) (by omega) h
          · -- n >= 594784172
            exact Brocard.berndt_galway_chunk_3308 n m (by omega) (by omega) h
      · -- n >= 594964028
        rcases Nat.lt_or_ge n 595503597 with hs3 | hs3
        · -- n < 595503597
          rcases Nat.lt_or_ge n 595323741 with hs4 | hs4
          · -- n < 595323741
            rcases Nat.lt_or_ge n 595143884 with hs5 | hs5
            · -- n < 595143884
              exact Brocard.berndt_galway_chunk_3309 n m (by omega) (by omega) h
            · -- n >= 595143884
              exact Brocard.berndt_galway_chunk_3310 n m (by omega) (by omega) h
          · -- n >= 595323741
            exact Brocard.berndt_galway_chunk_3311 n m (by omega) (by omega) h
        · -- n >= 595503597
          rcases Nat.lt_or_ge n 595683453 with hs4 | hs4
          · -- n < 595683453
            exact Brocard.berndt_galway_chunk_3312 n m (by omega) (by omega) h
          · -- n >= 595683453
            exact Brocard.berndt_galway_chunk_3313 n m (by omega) (by omega) h
  · -- n >= 595863309
    rcases Nat.lt_or_ge n 598021582 with hs1 | hs1
    · -- n < 598021582
      rcases Nat.lt_or_ge n 596942446 with hs2 | hs2
      · -- n < 596942446
        rcases Nat.lt_or_ge n 596402877 with hs3 | hs3
        · -- n < 596402877
          rcases Nat.lt_or_ge n 596223021 with hs4 | hs4
          · -- n < 596223021
            rcases Nat.lt_or_ge n 596043165 with hs5 | hs5
            · -- n < 596043165
              exact Brocard.berndt_galway_chunk_3314 n m (by omega) (by omega) h
            · -- n >= 596043165
              exact Brocard.berndt_galway_chunk_3315 n m (by omega) (by omega) h
          · -- n >= 596223021
            exact Brocard.berndt_galway_chunk_3316 n m (by omega) (by omega) h
        · -- n >= 596402877
          rcases Nat.lt_or_ge n 596762589 with hs4 | hs4
          · -- n < 596762589
            rcases Nat.lt_or_ge n 596582733 with hs5 | hs5
            · -- n < 596582733
              exact Brocard.berndt_galway_chunk_3317 n m (by omega) (by omega) h
            · -- n >= 596582733
              exact Brocard.berndt_galway_chunk_3318 n m (by omega) (by omega) h
          · -- n >= 596762589
            exact Brocard.berndt_galway_chunk_3319 n m (by omega) (by omega) h
      · -- n >= 596942446
        rcases Nat.lt_or_ge n 597482014 with hs3 | hs3
        · -- n < 597482014
          rcases Nat.lt_or_ge n 597302158 with hs4 | hs4
          · -- n < 597302158
            rcases Nat.lt_or_ge n 597122302 with hs5 | hs5
            · -- n < 597122302
              exact Brocard.berndt_galway_chunk_3320 n m (by omega) (by omega) h
            · -- n >= 597122302
              exact Brocard.berndt_galway_chunk_3321 n m (by omega) (by omega) h
          · -- n >= 597302158
            exact Brocard.berndt_galway_chunk_3322 n m (by omega) (by omega) h
        · -- n >= 597482014
          rcases Nat.lt_or_ge n 597841726 with hs4 | hs4
          · -- n < 597841726
            rcases Nat.lt_or_ge n 597661870 with hs5 | hs5
            · -- n < 597661870
              exact Brocard.berndt_galway_chunk_3323 n m (by omega) (by omega) h
            · -- n >= 597661870
              exact Brocard.berndt_galway_chunk_3324 n m (by omega) (by omega) h
          · -- n >= 597841726
            exact Brocard.berndt_galway_chunk_3325 n m (by omega) (by omega) h
    · -- n >= 598021582
      rcases Nat.lt_or_ge n 599100719 with hs2 | hs2
      · -- n < 599100719
        rcases Nat.lt_or_ge n 598561151 with hs3 | hs3
        · -- n < 598561151
          rcases Nat.lt_or_ge n 598381294 with hs4 | hs4
          · -- n < 598381294
            rcases Nat.lt_or_ge n 598201438 with hs5 | hs5
            · -- n < 598201438
              exact Brocard.berndt_galway_chunk_3326 n m (by omega) (by omega) h
            · -- n >= 598201438
              exact Brocard.berndt_galway_chunk_3327 n m (by omega) (by omega) h
          · -- n >= 598381294
            exact Brocard.berndt_galway_chunk_3328 n m (by omega) (by omega) h
        · -- n >= 598561151
          rcases Nat.lt_or_ge n 598920863 with hs4 | hs4
          · -- n < 598920863
            rcases Nat.lt_or_ge n 598741007 with hs5 | hs5
            · -- n < 598741007
              exact Brocard.berndt_galway_chunk_3329 n m (by omega) (by omega) h
            · -- n >= 598741007
              exact Brocard.berndt_galway_chunk_3330 n m (by omega) (by omega) h
          · -- n >= 598920863
            exact Brocard.berndt_galway_chunk_3331 n m (by omega) (by omega) h
      · -- n >= 599100719
        rcases Nat.lt_or_ge n 599640287 with hs3 | hs3
        · -- n < 599640287
          rcases Nat.lt_or_ge n 599460431 with hs4 | hs4
          · -- n < 599460431
            rcases Nat.lt_or_ge n 599280575 with hs5 | hs5
            · -- n < 599280575
              exact Brocard.berndt_galway_chunk_3332 n m (by omega) (by omega) h
            · -- n >= 599280575
              exact Brocard.berndt_galway_chunk_3333 n m (by omega) (by omega) h
          · -- n >= 599460431
            exact Brocard.berndt_galway_chunk_3334 n m (by omega) (by omega) h
        · -- n >= 599640287
          rcases Nat.lt_or_ge n 599820143 with hs4 | hs4
          · -- n < 599820143
            exact Brocard.berndt_galway_chunk_3335 n m (by omega) (by omega) h
          · -- n >= 599820143
            exact Brocard.berndt_galway_chunk_3336 n m (by omega) (by omega) h
