-- Prove2me | solution 1 for Brocard.berndt_galway_group_119
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:16:31.014996+00:00
-- url     : https://prove2.me/submissions/745d90a6-291b-41f1-a8d7-fd30fd7ed588

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_5469
import Theorems.Thm_Brocard_berndt_galway_chunk_5470
import Theorems.Thm_Brocard_berndt_galway_chunk_5471
import Theorems.Thm_Brocard_berndt_galway_chunk_5472
import Theorems.Thm_Brocard_berndt_galway_chunk_5473
import Theorems.Thm_Brocard_berndt_galway_chunk_5474
import Theorems.Thm_Brocard_berndt_galway_chunk_5475
import Theorems.Thm_Brocard_berndt_galway_chunk_5476
import Theorems.Thm_Brocard_berndt_galway_chunk_5477
import Theorems.Thm_Brocard_berndt_galway_chunk_5478
import Theorems.Thm_Brocard_berndt_galway_chunk_5479
import Theorems.Thm_Brocard_berndt_galway_chunk_5480
import Theorems.Thm_Brocard_berndt_galway_chunk_5481
import Theorems.Thm_Brocard_berndt_galway_chunk_5482
import Theorems.Thm_Brocard_berndt_galway_chunk_5483
import Theorems.Thm_Brocard_berndt_galway_chunk_5484
import Theorems.Thm_Brocard_berndt_galway_chunk_5485
import Theorems.Thm_Brocard_berndt_galway_chunk_5486
import Theorems.Thm_Brocard_berndt_galway_chunk_5487
import Theorems.Thm_Brocard_berndt_galway_chunk_5488
import Theorems.Thm_Brocard_berndt_galway_chunk_5489
import Theorems.Thm_Brocard_berndt_galway_chunk_5490
import Theorems.Thm_Brocard_berndt_galway_chunk_5491
import Theorems.Thm_Brocard_berndt_galway_chunk_5492
import Theorems.Thm_Brocard_berndt_galway_chunk_5493
import Theorems.Thm_Brocard_berndt_galway_chunk_5494
import Theorems.Thm_Brocard_berndt_galway_chunk_5495
import Theorems.Thm_Brocard_berndt_galway_chunk_5496
import Theorems.Thm_Brocard_berndt_galway_chunk_5497
import Theorems.Thm_Brocard_berndt_galway_chunk_5498
import Theorems.Thm_Brocard_berndt_galway_chunk_5499
import Theorems.Thm_Brocard_berndt_galway_chunk_5500
import Theorems.Thm_Brocard_berndt_galway_chunk_5501
import Theorems.Thm_Brocard_berndt_galway_chunk_5502
import Theorems.Thm_Brocard_berndt_galway_chunk_5503
import Theorems.Thm_Brocard_berndt_galway_chunk_5504
import Theorems.Thm_Brocard_berndt_galway_chunk_5505
import Theorems.Thm_Brocard_berndt_galway_chunk_5506
import Theorems.Thm_Brocard_berndt_galway_chunk_5507
import Theorems.Thm_Brocard_berndt_galway_chunk_5508
import Theorems.Thm_Brocard_berndt_galway_chunk_5509
import Theorems.Thm_Brocard_berndt_galway_chunk_5510
import Theorems.Thm_Brocard_berndt_galway_chunk_5511
import Theorems.Thm_Brocard_berndt_galway_chunk_5512
import Theorems.Thm_Brocard_berndt_galway_chunk_5513
import Theorems.Thm_Brocard_berndt_galway_chunk_5514

theorem solution (n m : ℕ) (h1 : 983453237 ≤ n) (h2 : n < 991726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 987589928 with hs0 | hs0
  · -- n < 987589928
    rcases Nat.lt_or_ge n 985611510 with hs1 | hs1
    · -- n < 985611510
      rcases Nat.lt_or_ge n 984532374 with hs2 | hs2
      · -- n < 984532374
        rcases Nat.lt_or_ge n 983992805 with hs3 | hs3
        · -- n < 983992805
          rcases Nat.lt_or_ge n 983812949 with hs4 | hs4
          · -- n < 983812949
            rcases Nat.lt_or_ge n 983633093 with hs5 | hs5
            · -- n < 983633093
              exact Brocard.berndt_galway_chunk_5469 n m (by omega) (by omega) h
            · -- n >= 983633093
              exact Brocard.berndt_galway_chunk_5470 n m (by omega) (by omega) h
          · -- n >= 983812949
            exact Brocard.berndt_galway_chunk_5471 n m (by omega) (by omega) h
        · -- n >= 983992805
          rcases Nat.lt_or_ge n 984352517 with hs4 | hs4
          · -- n < 984352517
            rcases Nat.lt_or_ge n 984172661 with hs5 | hs5
            · -- n < 984172661
              exact Brocard.berndt_galway_chunk_5472 n m (by omega) (by omega) h
            · -- n >= 984172661
              exact Brocard.berndt_galway_chunk_5473 n m (by omega) (by omega) h
          · -- n >= 984352517
            exact Brocard.berndt_galway_chunk_5474 n m (by omega) (by omega) h
      · -- n >= 984532374
        rcases Nat.lt_or_ge n 985071942 with hs3 | hs3
        · -- n < 985071942
          rcases Nat.lt_or_ge n 984892086 with hs4 | hs4
          · -- n < 984892086
            rcases Nat.lt_or_ge n 984712230 with hs5 | hs5
            · -- n < 984712230
              exact Brocard.berndt_galway_chunk_5475 n m (by omega) (by omega) h
            · -- n >= 984712230
              exact Brocard.berndt_galway_chunk_5476 n m (by omega) (by omega) h
          · -- n >= 984892086
            exact Brocard.berndt_galway_chunk_5477 n m (by omega) (by omega) h
        · -- n >= 985071942
          rcases Nat.lt_or_ge n 985431654 with hs4 | hs4
          · -- n < 985431654
            rcases Nat.lt_or_ge n 985251798 with hs5 | hs5
            · -- n < 985251798
              exact Brocard.berndt_galway_chunk_5478 n m (by omega) (by omega) h
            · -- n >= 985251798
              exact Brocard.berndt_galway_chunk_5479 n m (by omega) (by omega) h
          · -- n >= 985431654
            exact Brocard.berndt_galway_chunk_5480 n m (by omega) (by omega) h
    · -- n >= 985611510
      rcases Nat.lt_or_ge n 986690647 with hs2 | hs2
      · -- n < 986690647
        rcases Nat.lt_or_ge n 986151079 with hs3 | hs3
        · -- n < 986151079
          rcases Nat.lt_or_ge n 985971223 with hs4 | hs4
          · -- n < 985971223
            rcases Nat.lt_or_ge n 985791366 with hs5 | hs5
            · -- n < 985791366
              exact Brocard.berndt_galway_chunk_5481 n m (by omega) (by omega) h
            · -- n >= 985791366
              exact Brocard.berndt_galway_chunk_5482 n m (by omega) (by omega) h
          · -- n >= 985971223
            exact Brocard.berndt_galway_chunk_5483 n m (by omega) (by omega) h
        · -- n >= 986151079
          rcases Nat.lt_or_ge n 986510791 with hs4 | hs4
          · -- n < 986510791
            rcases Nat.lt_or_ge n 986330935 with hs5 | hs5
            · -- n < 986330935
              exact Brocard.berndt_galway_chunk_5484 n m (by omega) (by omega) h
            · -- n >= 986330935
              exact Brocard.berndt_galway_chunk_5485 n m (by omega) (by omega) h
          · -- n >= 986510791
            exact Brocard.berndt_galway_chunk_5486 n m (by omega) (by omega) h
      · -- n >= 986690647
        rcases Nat.lt_or_ge n 987230215 with hs3 | hs3
        · -- n < 987230215
          rcases Nat.lt_or_ge n 987050359 with hs4 | hs4
          · -- n < 987050359
            rcases Nat.lt_or_ge n 986870503 with hs5 | hs5
            · -- n < 986870503
              exact Brocard.berndt_galway_chunk_5487 n m (by omega) (by omega) h
            · -- n >= 986870503
              exact Brocard.berndt_galway_chunk_5488 n m (by omega) (by omega) h
          · -- n >= 987050359
            exact Brocard.berndt_galway_chunk_5489 n m (by omega) (by omega) h
        · -- n >= 987230215
          rcases Nat.lt_or_ge n 987410071 with hs4 | hs4
          · -- n < 987410071
            exact Brocard.berndt_galway_chunk_5490 n m (by omega) (by omega) h
          · -- n >= 987410071
            exact Brocard.berndt_galway_chunk_5491 n m (by omega) (by omega) h
  · -- n >= 987589928
    rcases Nat.lt_or_ge n 989748201 with hs1 | hs1
    · -- n < 989748201
      rcases Nat.lt_or_ge n 988669064 with hs2 | hs2
      · -- n < 988669064
        rcases Nat.lt_or_ge n 988129496 with hs3 | hs3
        · -- n < 988129496
          rcases Nat.lt_or_ge n 987949640 with hs4 | hs4
          · -- n < 987949640
            rcases Nat.lt_or_ge n 987769784 with hs5 | hs5
            · -- n < 987769784
              exact Brocard.berndt_galway_chunk_5492 n m (by omega) (by omega) h
            · -- n >= 987769784
              exact Brocard.berndt_galway_chunk_5493 n m (by omega) (by omega) h
          · -- n >= 987949640
            exact Brocard.berndt_galway_chunk_5494 n m (by omega) (by omega) h
        · -- n >= 988129496
          rcases Nat.lt_or_ge n 988489208 with hs4 | hs4
          · -- n < 988489208
            rcases Nat.lt_or_ge n 988309352 with hs5 | hs5
            · -- n < 988309352
              exact Brocard.berndt_galway_chunk_5495 n m (by omega) (by omega) h
            · -- n >= 988309352
              exact Brocard.berndt_galway_chunk_5496 n m (by omega) (by omega) h
          · -- n >= 988489208
            exact Brocard.berndt_galway_chunk_5497 n m (by omega) (by omega) h
      · -- n >= 988669064
        rcases Nat.lt_or_ge n 989208633 with hs3 | hs3
        · -- n < 989208633
          rcases Nat.lt_or_ge n 989028776 with hs4 | hs4
          · -- n < 989028776
            rcases Nat.lt_or_ge n 988848920 with hs5 | hs5
            · -- n < 988848920
              exact Brocard.berndt_galway_chunk_5498 n m (by omega) (by omega) h
            · -- n >= 988848920
              exact Brocard.berndt_galway_chunk_5499 n m (by omega) (by omega) h
          · -- n >= 989028776
            exact Brocard.berndt_galway_chunk_5500 n m (by omega) (by omega) h
        · -- n >= 989208633
          rcases Nat.lt_or_ge n 989568345 with hs4 | hs4
          · -- n < 989568345
            rcases Nat.lt_or_ge n 989388489 with hs5 | hs5
            · -- n < 989388489
              exact Brocard.berndt_galway_chunk_5501 n m (by omega) (by omega) h
            · -- n >= 989388489
              exact Brocard.berndt_galway_chunk_5502 n m (by omega) (by omega) h
          · -- n >= 989568345
            exact Brocard.berndt_galway_chunk_5503 n m (by omega) (by omega) h
    · -- n >= 989748201
      rcases Nat.lt_or_ge n 990827338 with hs2 | hs2
      · -- n < 990827338
        rcases Nat.lt_or_ge n 990287769 with hs3 | hs3
        · -- n < 990287769
          rcases Nat.lt_or_ge n 990107913 with hs4 | hs4
          · -- n < 990107913
            rcases Nat.lt_or_ge n 989928057 with hs5 | hs5
            · -- n < 989928057
              exact Brocard.berndt_galway_chunk_5504 n m (by omega) (by omega) h
            · -- n >= 989928057
              exact Brocard.berndt_galway_chunk_5505 n m (by omega) (by omega) h
          · -- n >= 990107913
            exact Brocard.berndt_galway_chunk_5506 n m (by omega) (by omega) h
        · -- n >= 990287769
          rcases Nat.lt_or_ge n 990647482 with hs4 | hs4
          · -- n < 990647482
            rcases Nat.lt_or_ge n 990467625 with hs5 | hs5
            · -- n < 990467625
              exact Brocard.berndt_galway_chunk_5507 n m (by omega) (by omega) h
            · -- n >= 990467625
              exact Brocard.berndt_galway_chunk_5508 n m (by omega) (by omega) h
          · -- n >= 990647482
            exact Brocard.berndt_galway_chunk_5509 n m (by omega) (by omega) h
      · -- n >= 990827338
        rcases Nat.lt_or_ge n 991366906 with hs3 | hs3
        · -- n < 991366906
          rcases Nat.lt_or_ge n 991187050 with hs4 | hs4
          · -- n < 991187050
            rcases Nat.lt_or_ge n 991007194 with hs5 | hs5
            · -- n < 991007194
              exact Brocard.berndt_galway_chunk_5510 n m (by omega) (by omega) h
            · -- n >= 991007194
              exact Brocard.berndt_galway_chunk_5511 n m (by omega) (by omega) h
          · -- n >= 991187050
            exact Brocard.berndt_galway_chunk_5512 n m (by omega) (by omega) h
        · -- n >= 991366906
          rcases Nat.lt_or_ge n 991546762 with hs4 | hs4
          · -- n < 991546762
            exact Brocard.berndt_galway_chunk_5513 n m (by omega) (by omega) h
          · -- n >= 991546762
            exact Brocard.berndt_galway_chunk_5514 n m (by omega) (by omega) h
