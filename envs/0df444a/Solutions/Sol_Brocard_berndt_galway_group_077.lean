-- Prove2me | solution 1 for Brocard.berndt_galway_group_077
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:11:31.993138+00:00
-- url     : https://prove2.me/submissions/7a36b9d2-bf60-4661-887d-7c3159058fe3

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_3525
import Theorems.Thm_Brocard_berndt_galway_chunk_3526
import Theorems.Thm_Brocard_berndt_galway_chunk_3527
import Theorems.Thm_Brocard_berndt_galway_chunk_3528
import Theorems.Thm_Brocard_berndt_galway_chunk_3529
import Theorems.Thm_Brocard_berndt_galway_chunk_3530
import Theorems.Thm_Brocard_berndt_galway_chunk_3531
import Theorems.Thm_Brocard_berndt_galway_chunk_3532
import Theorems.Thm_Brocard_berndt_galway_chunk_3533
import Theorems.Thm_Brocard_berndt_galway_chunk_3534
import Theorems.Thm_Brocard_berndt_galway_chunk_3535
import Theorems.Thm_Brocard_berndt_galway_chunk_3536
import Theorems.Thm_Brocard_berndt_galway_chunk_3537
import Theorems.Thm_Brocard_berndt_galway_chunk_3538
import Theorems.Thm_Brocard_berndt_galway_chunk_3539
import Theorems.Thm_Brocard_berndt_galway_chunk_3540
import Theorems.Thm_Brocard_berndt_galway_chunk_3541
import Theorems.Thm_Brocard_berndt_galway_chunk_3542
import Theorems.Thm_Brocard_berndt_galway_chunk_3543
import Theorems.Thm_Brocard_berndt_galway_chunk_3544
import Theorems.Thm_Brocard_berndt_galway_chunk_3545
import Theorems.Thm_Brocard_berndt_galway_chunk_3546
import Theorems.Thm_Brocard_berndt_galway_chunk_3547
import Theorems.Thm_Brocard_berndt_galway_chunk_3548
import Theorems.Thm_Brocard_berndt_galway_chunk_3549
import Theorems.Thm_Brocard_berndt_galway_chunk_3550
import Theorems.Thm_Brocard_berndt_galway_chunk_3551
import Theorems.Thm_Brocard_berndt_galway_chunk_3552
import Theorems.Thm_Brocard_berndt_galway_chunk_3553
import Theorems.Thm_Brocard_berndt_galway_chunk_3554
import Theorems.Thm_Brocard_berndt_galway_chunk_3555
import Theorems.Thm_Brocard_berndt_galway_chunk_3556
import Theorems.Thm_Brocard_berndt_galway_chunk_3557
import Theorems.Thm_Brocard_berndt_galway_chunk_3558
import Theorems.Thm_Brocard_berndt_galway_chunk_3559
import Theorems.Thm_Brocard_berndt_galway_chunk_3560
import Theorems.Thm_Brocard_berndt_galway_chunk_3561
import Theorems.Thm_Brocard_berndt_galway_chunk_3562
import Theorems.Thm_Brocard_berndt_galway_chunk_3563
import Theorems.Thm_Brocard_berndt_galway_chunk_3564
import Theorems.Thm_Brocard_berndt_galway_chunk_3565
import Theorems.Thm_Brocard_berndt_galway_chunk_3566
import Theorems.Thm_Brocard_berndt_galway_chunk_3567
import Theorems.Thm_Brocard_berndt_galway_chunk_3568
import Theorems.Thm_Brocard_berndt_galway_chunk_3569
import Theorems.Thm_Brocard_berndt_galway_chunk_3570

theorem solution (n m : ℕ) (h1 : 633812949 ≤ n) (h2 : n < 642086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 637949640 with hs0 | hs0
  · -- n < 637949640
    rcases Nat.lt_or_ge n 635971223 with hs1 | hs1
    · -- n < 635971223
      rcases Nat.lt_or_ge n 634892086 with hs2 | hs2
      · -- n < 634892086
        rcases Nat.lt_or_ge n 634352517 with hs3 | hs3
        · -- n < 634352517
          rcases Nat.lt_or_ge n 634172661 with hs4 | hs4
          · -- n < 634172661
            rcases Nat.lt_or_ge n 633992805 with hs5 | hs5
            · -- n < 633992805
              exact Brocard.berndt_galway_chunk_3525 n m (by omega) (by omega) h
            · -- n >= 633992805
              exact Brocard.berndt_galway_chunk_3526 n m (by omega) (by omega) h
          · -- n >= 634172661
            exact Brocard.berndt_galway_chunk_3527 n m (by omega) (by omega) h
        · -- n >= 634352517
          rcases Nat.lt_or_ge n 634712230 with hs4 | hs4
          · -- n < 634712230
            rcases Nat.lt_or_ge n 634532374 with hs5 | hs5
            · -- n < 634532374
              exact Brocard.berndt_galway_chunk_3528 n m (by omega) (by omega) h
            · -- n >= 634532374
              exact Brocard.berndt_galway_chunk_3529 n m (by omega) (by omega) h
          · -- n >= 634712230
            exact Brocard.berndt_galway_chunk_3530 n m (by omega) (by omega) h
      · -- n >= 634892086
        rcases Nat.lt_or_ge n 635431654 with hs3 | hs3
        · -- n < 635431654
          rcases Nat.lt_or_ge n 635251798 with hs4 | hs4
          · -- n < 635251798
            rcases Nat.lt_or_ge n 635071942 with hs5 | hs5
            · -- n < 635071942
              exact Brocard.berndt_galway_chunk_3531 n m (by omega) (by omega) h
            · -- n >= 635071942
              exact Brocard.berndt_galway_chunk_3532 n m (by omega) (by omega) h
          · -- n >= 635251798
            exact Brocard.berndt_galway_chunk_3533 n m (by omega) (by omega) h
        · -- n >= 635431654
          rcases Nat.lt_or_ge n 635791366 with hs4 | hs4
          · -- n < 635791366
            rcases Nat.lt_or_ge n 635611510 with hs5 | hs5
            · -- n < 635611510
              exact Brocard.berndt_galway_chunk_3534 n m (by omega) (by omega) h
            · -- n >= 635611510
              exact Brocard.berndt_galway_chunk_3535 n m (by omega) (by omega) h
          · -- n >= 635791366
            exact Brocard.berndt_galway_chunk_3536 n m (by omega) (by omega) h
    · -- n >= 635971223
      rcases Nat.lt_or_ge n 637050359 with hs2 | hs2
      · -- n < 637050359
        rcases Nat.lt_or_ge n 636510791 with hs3 | hs3
        · -- n < 636510791
          rcases Nat.lt_or_ge n 636330935 with hs4 | hs4
          · -- n < 636330935
            rcases Nat.lt_or_ge n 636151079 with hs5 | hs5
            · -- n < 636151079
              exact Brocard.berndt_galway_chunk_3537 n m (by omega) (by omega) h
            · -- n >= 636151079
              exact Brocard.berndt_galway_chunk_3538 n m (by omega) (by omega) h
          · -- n >= 636330935
            exact Brocard.berndt_galway_chunk_3539 n m (by omega) (by omega) h
        · -- n >= 636510791
          rcases Nat.lt_or_ge n 636870503 with hs4 | hs4
          · -- n < 636870503
            rcases Nat.lt_or_ge n 636690647 with hs5 | hs5
            · -- n < 636690647
              exact Brocard.berndt_galway_chunk_3540 n m (by omega) (by omega) h
            · -- n >= 636690647
              exact Brocard.berndt_galway_chunk_3541 n m (by omega) (by omega) h
          · -- n >= 636870503
            exact Brocard.berndt_galway_chunk_3542 n m (by omega) (by omega) h
      · -- n >= 637050359
        rcases Nat.lt_or_ge n 637589928 with hs3 | hs3
        · -- n < 637589928
          rcases Nat.lt_or_ge n 637410071 with hs4 | hs4
          · -- n < 637410071
            rcases Nat.lt_or_ge n 637230215 with hs5 | hs5
            · -- n < 637230215
              exact Brocard.berndt_galway_chunk_3543 n m (by omega) (by omega) h
            · -- n >= 637230215
              exact Brocard.berndt_galway_chunk_3544 n m (by omega) (by omega) h
          · -- n >= 637410071
            exact Brocard.berndt_galway_chunk_3545 n m (by omega) (by omega) h
        · -- n >= 637589928
          rcases Nat.lt_or_ge n 637769784 with hs4 | hs4
          · -- n < 637769784
            exact Brocard.berndt_galway_chunk_3546 n m (by omega) (by omega) h
          · -- n >= 637769784
            exact Brocard.berndt_galway_chunk_3547 n m (by omega) (by omega) h
  · -- n >= 637949640
    rcases Nat.lt_or_ge n 640107913 with hs1 | hs1
    · -- n < 640107913
      rcases Nat.lt_or_ge n 639028776 with hs2 | hs2
      · -- n < 639028776
        rcases Nat.lt_or_ge n 638489208 with hs3 | hs3
        · -- n < 638489208
          rcases Nat.lt_or_ge n 638309352 with hs4 | hs4
          · -- n < 638309352
            rcases Nat.lt_or_ge n 638129496 with hs5 | hs5
            · -- n < 638129496
              exact Brocard.berndt_galway_chunk_3548 n m (by omega) (by omega) h
            · -- n >= 638129496
              exact Brocard.berndt_galway_chunk_3549 n m (by omega) (by omega) h
          · -- n >= 638309352
            exact Brocard.berndt_galway_chunk_3550 n m (by omega) (by omega) h
        · -- n >= 638489208
          rcases Nat.lt_or_ge n 638848920 with hs4 | hs4
          · -- n < 638848920
            rcases Nat.lt_or_ge n 638669064 with hs5 | hs5
            · -- n < 638669064
              exact Brocard.berndt_galway_chunk_3551 n m (by omega) (by omega) h
            · -- n >= 638669064
              exact Brocard.berndt_galway_chunk_3552 n m (by omega) (by omega) h
          · -- n >= 638848920
            exact Brocard.berndt_galway_chunk_3553 n m (by omega) (by omega) h
      · -- n >= 639028776
        rcases Nat.lt_or_ge n 639568345 with hs3 | hs3
        · -- n < 639568345
          rcases Nat.lt_or_ge n 639388489 with hs4 | hs4
          · -- n < 639388489
            rcases Nat.lt_or_ge n 639208633 with hs5 | hs5
            · -- n < 639208633
              exact Brocard.berndt_galway_chunk_3554 n m (by omega) (by omega) h
            · -- n >= 639208633
              exact Brocard.berndt_galway_chunk_3555 n m (by omega) (by omega) h
          · -- n >= 639388489
            exact Brocard.berndt_galway_chunk_3556 n m (by omega) (by omega) h
        · -- n >= 639568345
          rcases Nat.lt_or_ge n 639928057 with hs4 | hs4
          · -- n < 639928057
            rcases Nat.lt_or_ge n 639748201 with hs5 | hs5
            · -- n < 639748201
              exact Brocard.berndt_galway_chunk_3557 n m (by omega) (by omega) h
            · -- n >= 639748201
              exact Brocard.berndt_galway_chunk_3558 n m (by omega) (by omega) h
          · -- n >= 639928057
            exact Brocard.berndt_galway_chunk_3559 n m (by omega) (by omega) h
    · -- n >= 640107913
      rcases Nat.lt_or_ge n 641187050 with hs2 | hs2
      · -- n < 641187050
        rcases Nat.lt_or_ge n 640647482 with hs3 | hs3
        · -- n < 640647482
          rcases Nat.lt_or_ge n 640467625 with hs4 | hs4
          · -- n < 640467625
            rcases Nat.lt_or_ge n 640287769 with hs5 | hs5
            · -- n < 640287769
              exact Brocard.berndt_galway_chunk_3560 n m (by omega) (by omega) h
            · -- n >= 640287769
              exact Brocard.berndt_galway_chunk_3561 n m (by omega) (by omega) h
          · -- n >= 640467625
            exact Brocard.berndt_galway_chunk_3562 n m (by omega) (by omega) h
        · -- n >= 640647482
          rcases Nat.lt_or_ge n 641007194 with hs4 | hs4
          · -- n < 641007194
            rcases Nat.lt_or_ge n 640827338 with hs5 | hs5
            · -- n < 640827338
              exact Brocard.berndt_galway_chunk_3563 n m (by omega) (by omega) h
            · -- n >= 640827338
              exact Brocard.berndt_galway_chunk_3564 n m (by omega) (by omega) h
          · -- n >= 641007194
            exact Brocard.berndt_galway_chunk_3565 n m (by omega) (by omega) h
      · -- n >= 641187050
        rcases Nat.lt_or_ge n 641726618 with hs3 | hs3
        · -- n < 641726618
          rcases Nat.lt_or_ge n 641546762 with hs4 | hs4
          · -- n < 641546762
            rcases Nat.lt_or_ge n 641366906 with hs5 | hs5
            · -- n < 641366906
              exact Brocard.berndt_galway_chunk_3566 n m (by omega) (by omega) h
            · -- n >= 641366906
              exact Brocard.berndt_galway_chunk_3567 n m (by omega) (by omega) h
          · -- n >= 641546762
            exact Brocard.berndt_galway_chunk_3568 n m (by omega) (by omega) h
        · -- n >= 641726618
          rcases Nat.lt_or_ge n 641906474 with hs4 | hs4
          · -- n < 641906474
            exact Brocard.berndt_galway_chunk_3569 n m (by omega) (by omega) h
          · -- n >= 641906474
            exact Brocard.berndt_galway_chunk_3570 n m (by omega) (by omega) h
