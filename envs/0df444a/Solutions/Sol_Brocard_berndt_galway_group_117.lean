-- Prove2me | solution 1 for Brocard.berndt_galway_group_117
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:55:47.470779+00:00
-- url     : https://prove2.me/submissions/63ec9c9f-1a8a-4b07-870a-7e7a5d8f4a44

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_5377
import Theorems.Thm_Brocard_berndt_galway_chunk_5378
import Theorems.Thm_Brocard_berndt_galway_chunk_5379
import Theorems.Thm_Brocard_berndt_galway_chunk_5380
import Theorems.Thm_Brocard_berndt_galway_chunk_5381
import Theorems.Thm_Brocard_berndt_galway_chunk_5382
import Theorems.Thm_Brocard_berndt_galway_chunk_5383
import Theorems.Thm_Brocard_berndt_galway_chunk_5384
import Theorems.Thm_Brocard_berndt_galway_chunk_5385
import Theorems.Thm_Brocard_berndt_galway_chunk_5386
import Theorems.Thm_Brocard_berndt_galway_chunk_5387
import Theorems.Thm_Brocard_berndt_galway_chunk_5388
import Theorems.Thm_Brocard_berndt_galway_chunk_5389
import Theorems.Thm_Brocard_berndt_galway_chunk_5390
import Theorems.Thm_Brocard_berndt_galway_chunk_5391
import Theorems.Thm_Brocard_berndt_galway_chunk_5392
import Theorems.Thm_Brocard_berndt_galway_chunk_5393
import Theorems.Thm_Brocard_berndt_galway_chunk_5394
import Theorems.Thm_Brocard_berndt_galway_chunk_5395
import Theorems.Thm_Brocard_berndt_galway_chunk_5396
import Theorems.Thm_Brocard_berndt_galway_chunk_5397
import Theorems.Thm_Brocard_berndt_galway_chunk_5398
import Theorems.Thm_Brocard_berndt_galway_chunk_5399
import Theorems.Thm_Brocard_berndt_galway_chunk_5400
import Theorems.Thm_Brocard_berndt_galway_chunk_5401
import Theorems.Thm_Brocard_berndt_galway_chunk_5402
import Theorems.Thm_Brocard_berndt_galway_chunk_5403
import Theorems.Thm_Brocard_berndt_galway_chunk_5404
import Theorems.Thm_Brocard_berndt_galway_chunk_5405
import Theorems.Thm_Brocard_berndt_galway_chunk_5406
import Theorems.Thm_Brocard_berndt_galway_chunk_5407
import Theorems.Thm_Brocard_berndt_galway_chunk_5408
import Theorems.Thm_Brocard_berndt_galway_chunk_5409
import Theorems.Thm_Brocard_berndt_galway_chunk_5410
import Theorems.Thm_Brocard_berndt_galway_chunk_5411
import Theorems.Thm_Brocard_berndt_galway_chunk_5412
import Theorems.Thm_Brocard_berndt_galway_chunk_5413
import Theorems.Thm_Brocard_berndt_galway_chunk_5414
import Theorems.Thm_Brocard_berndt_galway_chunk_5415
import Theorems.Thm_Brocard_berndt_galway_chunk_5416
import Theorems.Thm_Brocard_berndt_galway_chunk_5417
import Theorems.Thm_Brocard_berndt_galway_chunk_5418
import Theorems.Thm_Brocard_berndt_galway_chunk_5419
import Theorems.Thm_Brocard_berndt_galway_chunk_5420
import Theorems.Thm_Brocard_berndt_galway_chunk_5421
import Theorems.Thm_Brocard_berndt_galway_chunk_5422

theorem solution (n m : ℕ) (h1 : 966906474 ≤ n) (h2 : n < 975179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 971043165 with hs0 | hs0
  · -- n < 971043165
    rcases Nat.lt_or_ge n 969064748 with hs1 | hs1
    · -- n < 969064748
      rcases Nat.lt_or_ge n 967985611 with hs2 | hs2
      · -- n < 967985611
        rcases Nat.lt_or_ge n 967446043 with hs3 | hs3
        · -- n < 967446043
          rcases Nat.lt_or_ge n 967266187 with hs4 | hs4
          · -- n < 967266187
            rcases Nat.lt_or_ge n 967086330 with hs5 | hs5
            · -- n < 967086330
              exact Brocard.berndt_galway_chunk_5377 n m (by omega) (by omega) h
            · -- n >= 967086330
              exact Brocard.berndt_galway_chunk_5378 n m (by omega) (by omega) h
          · -- n >= 967266187
            exact Brocard.berndt_galway_chunk_5379 n m (by omega) (by omega) h
        · -- n >= 967446043
          rcases Nat.lt_or_ge n 967805755 with hs4 | hs4
          · -- n < 967805755
            rcases Nat.lt_or_ge n 967625899 with hs5 | hs5
            · -- n < 967625899
              exact Brocard.berndt_galway_chunk_5380 n m (by omega) (by omega) h
            · -- n >= 967625899
              exact Brocard.berndt_galway_chunk_5381 n m (by omega) (by omega) h
          · -- n >= 967805755
            exact Brocard.berndt_galway_chunk_5382 n m (by omega) (by omega) h
      · -- n >= 967985611
        rcases Nat.lt_or_ge n 968525179 with hs3 | hs3
        · -- n < 968525179
          rcases Nat.lt_or_ge n 968345323 with hs4 | hs4
          · -- n < 968345323
            rcases Nat.lt_or_ge n 968165467 with hs5 | hs5
            · -- n < 968165467
              exact Brocard.berndt_galway_chunk_5383 n m (by omega) (by omega) h
            · -- n >= 968165467
              exact Brocard.berndt_galway_chunk_5384 n m (by omega) (by omega) h
          · -- n >= 968345323
            exact Brocard.berndt_galway_chunk_5385 n m (by omega) (by omega) h
        · -- n >= 968525179
          rcases Nat.lt_or_ge n 968884892 with hs4 | hs4
          · -- n < 968884892
            rcases Nat.lt_or_ge n 968705035 with hs5 | hs5
            · -- n < 968705035
              exact Brocard.berndt_galway_chunk_5386 n m (by omega) (by omega) h
            · -- n >= 968705035
              exact Brocard.berndt_galway_chunk_5387 n m (by omega) (by omega) h
          · -- n >= 968884892
            exact Brocard.berndt_galway_chunk_5388 n m (by omega) (by omega) h
    · -- n >= 969064748
      rcases Nat.lt_or_ge n 970143884 with hs2 | hs2
      · -- n < 970143884
        rcases Nat.lt_or_ge n 969604316 with hs3 | hs3
        · -- n < 969604316
          rcases Nat.lt_or_ge n 969424460 with hs4 | hs4
          · -- n < 969424460
            rcases Nat.lt_or_ge n 969244604 with hs5 | hs5
            · -- n < 969244604
              exact Brocard.berndt_galway_chunk_5389 n m (by omega) (by omega) h
            · -- n >= 969244604
              exact Brocard.berndt_galway_chunk_5390 n m (by omega) (by omega) h
          · -- n >= 969424460
            exact Brocard.berndt_galway_chunk_5391 n m (by omega) (by omega) h
        · -- n >= 969604316
          rcases Nat.lt_or_ge n 969964028 with hs4 | hs4
          · -- n < 969964028
            rcases Nat.lt_or_ge n 969784172 with hs5 | hs5
            · -- n < 969784172
              exact Brocard.berndt_galway_chunk_5392 n m (by omega) (by omega) h
            · -- n >= 969784172
              exact Brocard.berndt_galway_chunk_5393 n m (by omega) (by omega) h
          · -- n >= 969964028
            exact Brocard.berndt_galway_chunk_5394 n m (by omega) (by omega) h
      · -- n >= 970143884
        rcases Nat.lt_or_ge n 970683453 with hs3 | hs3
        · -- n < 970683453
          rcases Nat.lt_or_ge n 970503597 with hs4 | hs4
          · -- n < 970503597
            rcases Nat.lt_or_ge n 970323741 with hs5 | hs5
            · -- n < 970323741
              exact Brocard.berndt_galway_chunk_5395 n m (by omega) (by omega) h
            · -- n >= 970323741
              exact Brocard.berndt_galway_chunk_5396 n m (by omega) (by omega) h
          · -- n >= 970503597
            exact Brocard.berndt_galway_chunk_5397 n m (by omega) (by omega) h
        · -- n >= 970683453
          rcases Nat.lt_or_ge n 970863309 with hs4 | hs4
          · -- n < 970863309
            exact Brocard.berndt_galway_chunk_5398 n m (by omega) (by omega) h
          · -- n >= 970863309
            exact Brocard.berndt_galway_chunk_5399 n m (by omega) (by omega) h
  · -- n >= 971043165
    rcases Nat.lt_or_ge n 973201438 with hs1 | hs1
    · -- n < 973201438
      rcases Nat.lt_or_ge n 972122302 with hs2 | hs2
      · -- n < 972122302
        rcases Nat.lt_or_ge n 971582733 with hs3 | hs3
        · -- n < 971582733
          rcases Nat.lt_or_ge n 971402877 with hs4 | hs4
          · -- n < 971402877
            rcases Nat.lt_or_ge n 971223021 with hs5 | hs5
            · -- n < 971223021
              exact Brocard.berndt_galway_chunk_5400 n m (by omega) (by omega) h
            · -- n >= 971223021
              exact Brocard.berndt_galway_chunk_5401 n m (by omega) (by omega) h
          · -- n >= 971402877
            exact Brocard.berndt_galway_chunk_5402 n m (by omega) (by omega) h
        · -- n >= 971582733
          rcases Nat.lt_or_ge n 971942446 with hs4 | hs4
          · -- n < 971942446
            rcases Nat.lt_or_ge n 971762589 with hs5 | hs5
            · -- n < 971762589
              exact Brocard.berndt_galway_chunk_5403 n m (by omega) (by omega) h
            · -- n >= 971762589
              exact Brocard.berndt_galway_chunk_5404 n m (by omega) (by omega) h
          · -- n >= 971942446
            exact Brocard.berndt_galway_chunk_5405 n m (by omega) (by omega) h
      · -- n >= 972122302
        rcases Nat.lt_or_ge n 972661870 with hs3 | hs3
        · -- n < 972661870
          rcases Nat.lt_or_ge n 972482014 with hs4 | hs4
          · -- n < 972482014
            rcases Nat.lt_or_ge n 972302158 with hs5 | hs5
            · -- n < 972302158
              exact Brocard.berndt_galway_chunk_5406 n m (by omega) (by omega) h
            · -- n >= 972302158
              exact Brocard.berndt_galway_chunk_5407 n m (by omega) (by omega) h
          · -- n >= 972482014
            exact Brocard.berndt_galway_chunk_5408 n m (by omega) (by omega) h
        · -- n >= 972661870
          rcases Nat.lt_or_ge n 973021582 with hs4 | hs4
          · -- n < 973021582
            rcases Nat.lt_or_ge n 972841726 with hs5 | hs5
            · -- n < 972841726
              exact Brocard.berndt_galway_chunk_5409 n m (by omega) (by omega) h
            · -- n >= 972841726
              exact Brocard.berndt_galway_chunk_5410 n m (by omega) (by omega) h
          · -- n >= 973021582
            exact Brocard.berndt_galway_chunk_5411 n m (by omega) (by omega) h
    · -- n >= 973201438
      rcases Nat.lt_or_ge n 974280575 with hs2 | hs2
      · -- n < 974280575
        rcases Nat.lt_or_ge n 973741007 with hs3 | hs3
        · -- n < 973741007
          rcases Nat.lt_or_ge n 973561151 with hs4 | hs4
          · -- n < 973561151
            rcases Nat.lt_or_ge n 973381294 with hs5 | hs5
            · -- n < 973381294
              exact Brocard.berndt_galway_chunk_5412 n m (by omega) (by omega) h
            · -- n >= 973381294
              exact Brocard.berndt_galway_chunk_5413 n m (by omega) (by omega) h
          · -- n >= 973561151
            exact Brocard.berndt_galway_chunk_5414 n m (by omega) (by omega) h
        · -- n >= 973741007
          rcases Nat.lt_or_ge n 974100719 with hs4 | hs4
          · -- n < 974100719
            rcases Nat.lt_or_ge n 973920863 with hs5 | hs5
            · -- n < 973920863
              exact Brocard.berndt_galway_chunk_5415 n m (by omega) (by omega) h
            · -- n >= 973920863
              exact Brocard.berndt_galway_chunk_5416 n m (by omega) (by omega) h
          · -- n >= 974100719
            exact Brocard.berndt_galway_chunk_5417 n m (by omega) (by omega) h
      · -- n >= 974280575
        rcases Nat.lt_or_ge n 974820143 with hs3 | hs3
        · -- n < 974820143
          rcases Nat.lt_or_ge n 974640287 with hs4 | hs4
          · -- n < 974640287
            rcases Nat.lt_or_ge n 974460431 with hs5 | hs5
            · -- n < 974460431
              exact Brocard.berndt_galway_chunk_5418 n m (by omega) (by omega) h
            · -- n >= 974460431
              exact Brocard.berndt_galway_chunk_5419 n m (by omega) (by omega) h
          · -- n >= 974640287
            exact Brocard.berndt_galway_chunk_5420 n m (by omega) (by omega) h
        · -- n >= 974820143
          rcases Nat.lt_or_ge n 975000000 with hs4 | hs4
          · -- n < 975000000
            exact Brocard.berndt_galway_chunk_5421 n m (by omega) (by omega) h
          · -- n >= 975000000
            exact Brocard.berndt_galway_chunk_5422 n m (by omega) (by omega) h
