-- Prove2me | solution 1 for Brocard.berndt_galway_group_095
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:38:25.984768+00:00
-- url     : https://prove2.me/submissions/a664b3b3-448b-463e-8f3a-1b6ef449d745

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_4357
import Theorems.Thm_Brocard_berndt_galway_chunk_4358
import Theorems.Thm_Brocard_berndt_galway_chunk_4359
import Theorems.Thm_Brocard_berndt_galway_chunk_4360
import Theorems.Thm_Brocard_berndt_galway_chunk_4361
import Theorems.Thm_Brocard_berndt_galway_chunk_4362
import Theorems.Thm_Brocard_berndt_galway_chunk_4363
import Theorems.Thm_Brocard_berndt_galway_chunk_4364
import Theorems.Thm_Brocard_berndt_galway_chunk_4365
import Theorems.Thm_Brocard_berndt_galway_chunk_4366
import Theorems.Thm_Brocard_berndt_galway_chunk_4367
import Theorems.Thm_Brocard_berndt_galway_chunk_4368
import Theorems.Thm_Brocard_berndt_galway_chunk_4369
import Theorems.Thm_Brocard_berndt_galway_chunk_4370
import Theorems.Thm_Brocard_berndt_galway_chunk_4371
import Theorems.Thm_Brocard_berndt_galway_chunk_4372
import Theorems.Thm_Brocard_berndt_galway_chunk_4373
import Theorems.Thm_Brocard_berndt_galway_chunk_4374
import Theorems.Thm_Brocard_berndt_galway_chunk_4375
import Theorems.Thm_Brocard_berndt_galway_chunk_4376
import Theorems.Thm_Brocard_berndt_galway_chunk_4377
import Theorems.Thm_Brocard_berndt_galway_chunk_4378
import Theorems.Thm_Brocard_berndt_galway_chunk_4379
import Theorems.Thm_Brocard_berndt_galway_chunk_4380
import Theorems.Thm_Brocard_berndt_galway_chunk_4381
import Theorems.Thm_Brocard_berndt_galway_chunk_4382
import Theorems.Thm_Brocard_berndt_galway_chunk_4383
import Theorems.Thm_Brocard_berndt_galway_chunk_4384
import Theorems.Thm_Brocard_berndt_galway_chunk_4385
import Theorems.Thm_Brocard_berndt_galway_chunk_4386
import Theorems.Thm_Brocard_berndt_galway_chunk_4387
import Theorems.Thm_Brocard_berndt_galway_chunk_4388
import Theorems.Thm_Brocard_berndt_galway_chunk_4389
import Theorems.Thm_Brocard_berndt_galway_chunk_4390
import Theorems.Thm_Brocard_berndt_galway_chunk_4391
import Theorems.Thm_Brocard_berndt_galway_chunk_4392
import Theorems.Thm_Brocard_berndt_galway_chunk_4393
import Theorems.Thm_Brocard_berndt_galway_chunk_4394
import Theorems.Thm_Brocard_berndt_galway_chunk_4395
import Theorems.Thm_Brocard_berndt_galway_chunk_4396
import Theorems.Thm_Brocard_berndt_galway_chunk_4397
import Theorems.Thm_Brocard_berndt_galway_chunk_4398
import Theorems.Thm_Brocard_berndt_galway_chunk_4399
import Theorems.Thm_Brocard_berndt_galway_chunk_4400
import Theorems.Thm_Brocard_berndt_galway_chunk_4401
import Theorems.Thm_Brocard_berndt_galway_chunk_4402

theorem solution (n m : ℕ) (h1 : 783453237 ≤ n) (h2 : n < 791726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 787589928 with hs0 | hs0
  · -- n < 787589928
    rcases Nat.lt_or_ge n 785611510 with hs1 | hs1
    · -- n < 785611510
      rcases Nat.lt_or_ge n 784532374 with hs2 | hs2
      · -- n < 784532374
        rcases Nat.lt_or_ge n 783992805 with hs3 | hs3
        · -- n < 783992805
          rcases Nat.lt_or_ge n 783812949 with hs4 | hs4
          · -- n < 783812949
            rcases Nat.lt_or_ge n 783633093 with hs5 | hs5
            · -- n < 783633093
              exact Brocard.berndt_galway_chunk_4357 n m (by omega) (by omega) h
            · -- n >= 783633093
              exact Brocard.berndt_galway_chunk_4358 n m (by omega) (by omega) h
          · -- n >= 783812949
            exact Brocard.berndt_galway_chunk_4359 n m (by omega) (by omega) h
        · -- n >= 783992805
          rcases Nat.lt_or_ge n 784352517 with hs4 | hs4
          · -- n < 784352517
            rcases Nat.lt_or_ge n 784172661 with hs5 | hs5
            · -- n < 784172661
              exact Brocard.berndt_galway_chunk_4360 n m (by omega) (by omega) h
            · -- n >= 784172661
              exact Brocard.berndt_galway_chunk_4361 n m (by omega) (by omega) h
          · -- n >= 784352517
            exact Brocard.berndt_galway_chunk_4362 n m (by omega) (by omega) h
      · -- n >= 784532374
        rcases Nat.lt_or_ge n 785071942 with hs3 | hs3
        · -- n < 785071942
          rcases Nat.lt_or_ge n 784892086 with hs4 | hs4
          · -- n < 784892086
            rcases Nat.lt_or_ge n 784712230 with hs5 | hs5
            · -- n < 784712230
              exact Brocard.berndt_galway_chunk_4363 n m (by omega) (by omega) h
            · -- n >= 784712230
              exact Brocard.berndt_galway_chunk_4364 n m (by omega) (by omega) h
          · -- n >= 784892086
            exact Brocard.berndt_galway_chunk_4365 n m (by omega) (by omega) h
        · -- n >= 785071942
          rcases Nat.lt_or_ge n 785431654 with hs4 | hs4
          · -- n < 785431654
            rcases Nat.lt_or_ge n 785251798 with hs5 | hs5
            · -- n < 785251798
              exact Brocard.berndt_galway_chunk_4366 n m (by omega) (by omega) h
            · -- n >= 785251798
              exact Brocard.berndt_galway_chunk_4367 n m (by omega) (by omega) h
          · -- n >= 785431654
            exact Brocard.berndt_galway_chunk_4368 n m (by omega) (by omega) h
    · -- n >= 785611510
      rcases Nat.lt_or_ge n 786690647 with hs2 | hs2
      · -- n < 786690647
        rcases Nat.lt_or_ge n 786151079 with hs3 | hs3
        · -- n < 786151079
          rcases Nat.lt_or_ge n 785971223 with hs4 | hs4
          · -- n < 785971223
            rcases Nat.lt_or_ge n 785791366 with hs5 | hs5
            · -- n < 785791366
              exact Brocard.berndt_galway_chunk_4369 n m (by omega) (by omega) h
            · -- n >= 785791366
              exact Brocard.berndt_galway_chunk_4370 n m (by omega) (by omega) h
          · -- n >= 785971223
            exact Brocard.berndt_galway_chunk_4371 n m (by omega) (by omega) h
        · -- n >= 786151079
          rcases Nat.lt_or_ge n 786510791 with hs4 | hs4
          · -- n < 786510791
            rcases Nat.lt_or_ge n 786330935 with hs5 | hs5
            · -- n < 786330935
              exact Brocard.berndt_galway_chunk_4372 n m (by omega) (by omega) h
            · -- n >= 786330935
              exact Brocard.berndt_galway_chunk_4373 n m (by omega) (by omega) h
          · -- n >= 786510791
            exact Brocard.berndt_galway_chunk_4374 n m (by omega) (by omega) h
      · -- n >= 786690647
        rcases Nat.lt_or_ge n 787230215 with hs3 | hs3
        · -- n < 787230215
          rcases Nat.lt_or_ge n 787050359 with hs4 | hs4
          · -- n < 787050359
            rcases Nat.lt_or_ge n 786870503 with hs5 | hs5
            · -- n < 786870503
              exact Brocard.berndt_galway_chunk_4375 n m (by omega) (by omega) h
            · -- n >= 786870503
              exact Brocard.berndt_galway_chunk_4376 n m (by omega) (by omega) h
          · -- n >= 787050359
            exact Brocard.berndt_galway_chunk_4377 n m (by omega) (by omega) h
        · -- n >= 787230215
          rcases Nat.lt_or_ge n 787410071 with hs4 | hs4
          · -- n < 787410071
            exact Brocard.berndt_galway_chunk_4378 n m (by omega) (by omega) h
          · -- n >= 787410071
            exact Brocard.berndt_galway_chunk_4379 n m (by omega) (by omega) h
  · -- n >= 787589928
    rcases Nat.lt_or_ge n 789748201 with hs1 | hs1
    · -- n < 789748201
      rcases Nat.lt_or_ge n 788669064 with hs2 | hs2
      · -- n < 788669064
        rcases Nat.lt_or_ge n 788129496 with hs3 | hs3
        · -- n < 788129496
          rcases Nat.lt_or_ge n 787949640 with hs4 | hs4
          · -- n < 787949640
            rcases Nat.lt_or_ge n 787769784 with hs5 | hs5
            · -- n < 787769784
              exact Brocard.berndt_galway_chunk_4380 n m (by omega) (by omega) h
            · -- n >= 787769784
              exact Brocard.berndt_galway_chunk_4381 n m (by omega) (by omega) h
          · -- n >= 787949640
            exact Brocard.berndt_galway_chunk_4382 n m (by omega) (by omega) h
        · -- n >= 788129496
          rcases Nat.lt_or_ge n 788489208 with hs4 | hs4
          · -- n < 788489208
            rcases Nat.lt_or_ge n 788309352 with hs5 | hs5
            · -- n < 788309352
              exact Brocard.berndt_galway_chunk_4383 n m (by omega) (by omega) h
            · -- n >= 788309352
              exact Brocard.berndt_galway_chunk_4384 n m (by omega) (by omega) h
          · -- n >= 788489208
            exact Brocard.berndt_galway_chunk_4385 n m (by omega) (by omega) h
      · -- n >= 788669064
        rcases Nat.lt_or_ge n 789208633 with hs3 | hs3
        · -- n < 789208633
          rcases Nat.lt_or_ge n 789028776 with hs4 | hs4
          · -- n < 789028776
            rcases Nat.lt_or_ge n 788848920 with hs5 | hs5
            · -- n < 788848920
              exact Brocard.berndt_galway_chunk_4386 n m (by omega) (by omega) h
            · -- n >= 788848920
              exact Brocard.berndt_galway_chunk_4387 n m (by omega) (by omega) h
          · -- n >= 789028776
            exact Brocard.berndt_galway_chunk_4388 n m (by omega) (by omega) h
        · -- n >= 789208633
          rcases Nat.lt_or_ge n 789568345 with hs4 | hs4
          · -- n < 789568345
            rcases Nat.lt_or_ge n 789388489 with hs5 | hs5
            · -- n < 789388489
              exact Brocard.berndt_galway_chunk_4389 n m (by omega) (by omega) h
            · -- n >= 789388489
              exact Brocard.berndt_galway_chunk_4390 n m (by omega) (by omega) h
          · -- n >= 789568345
            exact Brocard.berndt_galway_chunk_4391 n m (by omega) (by omega) h
    · -- n >= 789748201
      rcases Nat.lt_or_ge n 790827338 with hs2 | hs2
      · -- n < 790827338
        rcases Nat.lt_or_ge n 790287769 with hs3 | hs3
        · -- n < 790287769
          rcases Nat.lt_or_ge n 790107913 with hs4 | hs4
          · -- n < 790107913
            rcases Nat.lt_or_ge n 789928057 with hs5 | hs5
            · -- n < 789928057
              exact Brocard.berndt_galway_chunk_4392 n m (by omega) (by omega) h
            · -- n >= 789928057
              exact Brocard.berndt_galway_chunk_4393 n m (by omega) (by omega) h
          · -- n >= 790107913
            exact Brocard.berndt_galway_chunk_4394 n m (by omega) (by omega) h
        · -- n >= 790287769
          rcases Nat.lt_or_ge n 790647482 with hs4 | hs4
          · -- n < 790647482
            rcases Nat.lt_or_ge n 790467625 with hs5 | hs5
            · -- n < 790467625
              exact Brocard.berndt_galway_chunk_4395 n m (by omega) (by omega) h
            · -- n >= 790467625
              exact Brocard.berndt_galway_chunk_4396 n m (by omega) (by omega) h
          · -- n >= 790647482
            exact Brocard.berndt_galway_chunk_4397 n m (by omega) (by omega) h
      · -- n >= 790827338
        rcases Nat.lt_or_ge n 791366906 with hs3 | hs3
        · -- n < 791366906
          rcases Nat.lt_or_ge n 791187050 with hs4 | hs4
          · -- n < 791187050
            rcases Nat.lt_or_ge n 791007194 with hs5 | hs5
            · -- n < 791007194
              exact Brocard.berndt_galway_chunk_4398 n m (by omega) (by omega) h
            · -- n >= 791007194
              exact Brocard.berndt_galway_chunk_4399 n m (by omega) (by omega) h
          · -- n >= 791187050
            exact Brocard.berndt_galway_chunk_4400 n m (by omega) (by omega) h
        · -- n >= 791366906
          rcases Nat.lt_or_ge n 791546762 with hs4 | hs4
          · -- n < 791546762
            exact Brocard.berndt_galway_chunk_4401 n m (by omega) (by omega) h
          · -- n >= 791546762
            exact Brocard.berndt_galway_chunk_4402 n m (by omega) (by omega) h
