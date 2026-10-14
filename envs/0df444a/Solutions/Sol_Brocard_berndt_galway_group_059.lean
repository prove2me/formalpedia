-- Prove2me | solution 1 for Brocard.berndt_galway_group_059
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:42:41.383875+00:00
-- url     : https://prove2.me/submissions/46e8d9ad-f19e-458b-9f9f-07bcbb8a401b

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_2689
import Theorems.Thm_Brocard_berndt_galway_chunk_2690
import Theorems.Thm_Brocard_berndt_galway_chunk_2691
import Theorems.Thm_Brocard_berndt_galway_chunk_2692
import Theorems.Thm_Brocard_berndt_galway_chunk_2693
import Theorems.Thm_Brocard_berndt_galway_chunk_2694
import Theorems.Thm_Brocard_berndt_galway_chunk_2695
import Theorems.Thm_Brocard_berndt_galway_chunk_2696
import Theorems.Thm_Brocard_berndt_galway_chunk_2697
import Theorems.Thm_Brocard_berndt_galway_chunk_2698
import Theorems.Thm_Brocard_berndt_galway_chunk_2699
import Theorems.Thm_Brocard_berndt_galway_chunk_2700
import Theorems.Thm_Brocard_berndt_galway_chunk_2701
import Theorems.Thm_Brocard_berndt_galway_chunk_2702
import Theorems.Thm_Brocard_berndt_galway_chunk_2703
import Theorems.Thm_Brocard_berndt_galway_chunk_2704
import Theorems.Thm_Brocard_berndt_galway_chunk_2705
import Theorems.Thm_Brocard_berndt_galway_chunk_2706
import Theorems.Thm_Brocard_berndt_galway_chunk_2707
import Theorems.Thm_Brocard_berndt_galway_chunk_2708
import Theorems.Thm_Brocard_berndt_galway_chunk_2709
import Theorems.Thm_Brocard_berndt_galway_chunk_2710
import Theorems.Thm_Brocard_berndt_galway_chunk_2711
import Theorems.Thm_Brocard_berndt_galway_chunk_2712
import Theorems.Thm_Brocard_berndt_galway_chunk_2713
import Theorems.Thm_Brocard_berndt_galway_chunk_2714
import Theorems.Thm_Brocard_berndt_galway_chunk_2715
import Theorems.Thm_Brocard_berndt_galway_chunk_2716
import Theorems.Thm_Brocard_berndt_galway_chunk_2717
import Theorems.Thm_Brocard_berndt_galway_chunk_2718
import Theorems.Thm_Brocard_berndt_galway_chunk_2719
import Theorems.Thm_Brocard_berndt_galway_chunk_2720
import Theorems.Thm_Brocard_berndt_galway_chunk_2721
import Theorems.Thm_Brocard_berndt_galway_chunk_2722
import Theorems.Thm_Brocard_berndt_galway_chunk_2723
import Theorems.Thm_Brocard_berndt_galway_chunk_2724
import Theorems.Thm_Brocard_berndt_galway_chunk_2725
import Theorems.Thm_Brocard_berndt_galway_chunk_2726
import Theorems.Thm_Brocard_berndt_galway_chunk_2727
import Theorems.Thm_Brocard_berndt_galway_chunk_2728
import Theorems.Thm_Brocard_berndt_galway_chunk_2729
import Theorems.Thm_Brocard_berndt_galway_chunk_2730
import Theorems.Thm_Brocard_berndt_galway_chunk_2731
import Theorems.Thm_Brocard_berndt_galway_chunk_2732
import Theorems.Thm_Brocard_berndt_galway_chunk_2733
import Theorems.Thm_Brocard_berndt_galway_chunk_2734

theorem solution (n m : ℕ) (h1 : 483453237 ≤ n) (h2 : n < 491726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 487589928 with hs0 | hs0
  · -- n < 487589928
    rcases Nat.lt_or_ge n 485611510 with hs1 | hs1
    · -- n < 485611510
      rcases Nat.lt_or_ge n 484532374 with hs2 | hs2
      · -- n < 484532374
        rcases Nat.lt_or_ge n 483992805 with hs3 | hs3
        · -- n < 483992805
          rcases Nat.lt_or_ge n 483812949 with hs4 | hs4
          · -- n < 483812949
            rcases Nat.lt_or_ge n 483633093 with hs5 | hs5
            · -- n < 483633093
              exact Brocard.berndt_galway_chunk_2689 n m (by omega) (by omega) h
            · -- n >= 483633093
              exact Brocard.berndt_galway_chunk_2690 n m (by omega) (by omega) h
          · -- n >= 483812949
            exact Brocard.berndt_galway_chunk_2691 n m (by omega) (by omega) h
        · -- n >= 483992805
          rcases Nat.lt_or_ge n 484352517 with hs4 | hs4
          · -- n < 484352517
            rcases Nat.lt_or_ge n 484172661 with hs5 | hs5
            · -- n < 484172661
              exact Brocard.berndt_galway_chunk_2692 n m (by omega) (by omega) h
            · -- n >= 484172661
              exact Brocard.berndt_galway_chunk_2693 n m (by omega) (by omega) h
          · -- n >= 484352517
            exact Brocard.berndt_galway_chunk_2694 n m (by omega) (by omega) h
      · -- n >= 484532374
        rcases Nat.lt_or_ge n 485071942 with hs3 | hs3
        · -- n < 485071942
          rcases Nat.lt_or_ge n 484892086 with hs4 | hs4
          · -- n < 484892086
            rcases Nat.lt_or_ge n 484712230 with hs5 | hs5
            · -- n < 484712230
              exact Brocard.berndt_galway_chunk_2695 n m (by omega) (by omega) h
            · -- n >= 484712230
              exact Brocard.berndt_galway_chunk_2696 n m (by omega) (by omega) h
          · -- n >= 484892086
            exact Brocard.berndt_galway_chunk_2697 n m (by omega) (by omega) h
        · -- n >= 485071942
          rcases Nat.lt_or_ge n 485431654 with hs4 | hs4
          · -- n < 485431654
            rcases Nat.lt_or_ge n 485251798 with hs5 | hs5
            · -- n < 485251798
              exact Brocard.berndt_galway_chunk_2698 n m (by omega) (by omega) h
            · -- n >= 485251798
              exact Brocard.berndt_galway_chunk_2699 n m (by omega) (by omega) h
          · -- n >= 485431654
            exact Brocard.berndt_galway_chunk_2700 n m (by omega) (by omega) h
    · -- n >= 485611510
      rcases Nat.lt_or_ge n 486690647 with hs2 | hs2
      · -- n < 486690647
        rcases Nat.lt_or_ge n 486151079 with hs3 | hs3
        · -- n < 486151079
          rcases Nat.lt_or_ge n 485971223 with hs4 | hs4
          · -- n < 485971223
            rcases Nat.lt_or_ge n 485791366 with hs5 | hs5
            · -- n < 485791366
              exact Brocard.berndt_galway_chunk_2701 n m (by omega) (by omega) h
            · -- n >= 485791366
              exact Brocard.berndt_galway_chunk_2702 n m (by omega) (by omega) h
          · -- n >= 485971223
            exact Brocard.berndt_galway_chunk_2703 n m (by omega) (by omega) h
        · -- n >= 486151079
          rcases Nat.lt_or_ge n 486510791 with hs4 | hs4
          · -- n < 486510791
            rcases Nat.lt_or_ge n 486330935 with hs5 | hs5
            · -- n < 486330935
              exact Brocard.berndt_galway_chunk_2704 n m (by omega) (by omega) h
            · -- n >= 486330935
              exact Brocard.berndt_galway_chunk_2705 n m (by omega) (by omega) h
          · -- n >= 486510791
            exact Brocard.berndt_galway_chunk_2706 n m (by omega) (by omega) h
      · -- n >= 486690647
        rcases Nat.lt_or_ge n 487230215 with hs3 | hs3
        · -- n < 487230215
          rcases Nat.lt_or_ge n 487050359 with hs4 | hs4
          · -- n < 487050359
            rcases Nat.lt_or_ge n 486870503 with hs5 | hs5
            · -- n < 486870503
              exact Brocard.berndt_galway_chunk_2707 n m (by omega) (by omega) h
            · -- n >= 486870503
              exact Brocard.berndt_galway_chunk_2708 n m (by omega) (by omega) h
          · -- n >= 487050359
            exact Brocard.berndt_galway_chunk_2709 n m (by omega) (by omega) h
        · -- n >= 487230215
          rcases Nat.lt_or_ge n 487410071 with hs4 | hs4
          · -- n < 487410071
            exact Brocard.berndt_galway_chunk_2710 n m (by omega) (by omega) h
          · -- n >= 487410071
            exact Brocard.berndt_galway_chunk_2711 n m (by omega) (by omega) h
  · -- n >= 487589928
    rcases Nat.lt_or_ge n 489748201 with hs1 | hs1
    · -- n < 489748201
      rcases Nat.lt_or_ge n 488669064 with hs2 | hs2
      · -- n < 488669064
        rcases Nat.lt_or_ge n 488129496 with hs3 | hs3
        · -- n < 488129496
          rcases Nat.lt_or_ge n 487949640 with hs4 | hs4
          · -- n < 487949640
            rcases Nat.lt_or_ge n 487769784 with hs5 | hs5
            · -- n < 487769784
              exact Brocard.berndt_galway_chunk_2712 n m (by omega) (by omega) h
            · -- n >= 487769784
              exact Brocard.berndt_galway_chunk_2713 n m (by omega) (by omega) h
          · -- n >= 487949640
            exact Brocard.berndt_galway_chunk_2714 n m (by omega) (by omega) h
        · -- n >= 488129496
          rcases Nat.lt_or_ge n 488489208 with hs4 | hs4
          · -- n < 488489208
            rcases Nat.lt_or_ge n 488309352 with hs5 | hs5
            · -- n < 488309352
              exact Brocard.berndt_galway_chunk_2715 n m (by omega) (by omega) h
            · -- n >= 488309352
              exact Brocard.berndt_galway_chunk_2716 n m (by omega) (by omega) h
          · -- n >= 488489208
            exact Brocard.berndt_galway_chunk_2717 n m (by omega) (by omega) h
      · -- n >= 488669064
        rcases Nat.lt_or_ge n 489208633 with hs3 | hs3
        · -- n < 489208633
          rcases Nat.lt_or_ge n 489028776 with hs4 | hs4
          · -- n < 489028776
            rcases Nat.lt_or_ge n 488848920 with hs5 | hs5
            · -- n < 488848920
              exact Brocard.berndt_galway_chunk_2718 n m (by omega) (by omega) h
            · -- n >= 488848920
              exact Brocard.berndt_galway_chunk_2719 n m (by omega) (by omega) h
          · -- n >= 489028776
            exact Brocard.berndt_galway_chunk_2720 n m (by omega) (by omega) h
        · -- n >= 489208633
          rcases Nat.lt_or_ge n 489568345 with hs4 | hs4
          · -- n < 489568345
            rcases Nat.lt_or_ge n 489388489 with hs5 | hs5
            · -- n < 489388489
              exact Brocard.berndt_galway_chunk_2721 n m (by omega) (by omega) h
            · -- n >= 489388489
              exact Brocard.berndt_galway_chunk_2722 n m (by omega) (by omega) h
          · -- n >= 489568345
            exact Brocard.berndt_galway_chunk_2723 n m (by omega) (by omega) h
    · -- n >= 489748201
      rcases Nat.lt_or_ge n 490827338 with hs2 | hs2
      · -- n < 490827338
        rcases Nat.lt_or_ge n 490287769 with hs3 | hs3
        · -- n < 490287769
          rcases Nat.lt_or_ge n 490107913 with hs4 | hs4
          · -- n < 490107913
            rcases Nat.lt_or_ge n 489928057 with hs5 | hs5
            · -- n < 489928057
              exact Brocard.berndt_galway_chunk_2724 n m (by omega) (by omega) h
            · -- n >= 489928057
              exact Brocard.berndt_galway_chunk_2725 n m (by omega) (by omega) h
          · -- n >= 490107913
            exact Brocard.berndt_galway_chunk_2726 n m (by omega) (by omega) h
        · -- n >= 490287769
          rcases Nat.lt_or_ge n 490647482 with hs4 | hs4
          · -- n < 490647482
            rcases Nat.lt_or_ge n 490467625 with hs5 | hs5
            · -- n < 490467625
              exact Brocard.berndt_galway_chunk_2727 n m (by omega) (by omega) h
            · -- n >= 490467625
              exact Brocard.berndt_galway_chunk_2728 n m (by omega) (by omega) h
          · -- n >= 490647482
            exact Brocard.berndt_galway_chunk_2729 n m (by omega) (by omega) h
      · -- n >= 490827338
        rcases Nat.lt_or_ge n 491366906 with hs3 | hs3
        · -- n < 491366906
          rcases Nat.lt_or_ge n 491187050 with hs4 | hs4
          · -- n < 491187050
            rcases Nat.lt_or_ge n 491007194 with hs5 | hs5
            · -- n < 491007194
              exact Brocard.berndt_galway_chunk_2730 n m (by omega) (by omega) h
            · -- n >= 491007194
              exact Brocard.berndt_galway_chunk_2731 n m (by omega) (by omega) h
          · -- n >= 491187050
            exact Brocard.berndt_galway_chunk_2732 n m (by omega) (by omega) h
        · -- n >= 491366906
          rcases Nat.lt_or_ge n 491546762 with hs4 | hs4
          · -- n < 491546762
            exact Brocard.berndt_galway_chunk_2733 n m (by omega) (by omega) h
          · -- n >= 491546762
            exact Brocard.berndt_galway_chunk_2734 n m (by omega) (by omega) h
