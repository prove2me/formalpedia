-- Prove2me | solution 1 for Brocard.berndt_galway_group_081
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:40:42.585209+00:00
-- url     : https://prove2.me/submissions/39750be3-ae63-43cd-b24e-ea3ff2127636

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_3709
import Theorems.Thm_Brocard_berndt_galway_chunk_3710
import Theorems.Thm_Brocard_berndt_galway_chunk_3711
import Theorems.Thm_Brocard_berndt_galway_chunk_3712
import Theorems.Thm_Brocard_berndt_galway_chunk_3713
import Theorems.Thm_Brocard_berndt_galway_chunk_3714
import Theorems.Thm_Brocard_berndt_galway_chunk_3715
import Theorems.Thm_Brocard_berndt_galway_chunk_3716
import Theorems.Thm_Brocard_berndt_galway_chunk_3717
import Theorems.Thm_Brocard_berndt_galway_chunk_3718
import Theorems.Thm_Brocard_berndt_galway_chunk_3719
import Theorems.Thm_Brocard_berndt_galway_chunk_3720
import Theorems.Thm_Brocard_berndt_galway_chunk_3721
import Theorems.Thm_Brocard_berndt_galway_chunk_3722
import Theorems.Thm_Brocard_berndt_galway_chunk_3723
import Theorems.Thm_Brocard_berndt_galway_chunk_3724
import Theorems.Thm_Brocard_berndt_galway_chunk_3725
import Theorems.Thm_Brocard_berndt_galway_chunk_3726
import Theorems.Thm_Brocard_berndt_galway_chunk_3727
import Theorems.Thm_Brocard_berndt_galway_chunk_3728
import Theorems.Thm_Brocard_berndt_galway_chunk_3729
import Theorems.Thm_Brocard_berndt_galway_chunk_3730
import Theorems.Thm_Brocard_berndt_galway_chunk_3731
import Theorems.Thm_Brocard_berndt_galway_chunk_3732
import Theorems.Thm_Brocard_berndt_galway_chunk_3733
import Theorems.Thm_Brocard_berndt_galway_chunk_3734
import Theorems.Thm_Brocard_berndt_galway_chunk_3735
import Theorems.Thm_Brocard_berndt_galway_chunk_3736
import Theorems.Thm_Brocard_berndt_galway_chunk_3737
import Theorems.Thm_Brocard_berndt_galway_chunk_3738
import Theorems.Thm_Brocard_berndt_galway_chunk_3739
import Theorems.Thm_Brocard_berndt_galway_chunk_3740
import Theorems.Thm_Brocard_berndt_galway_chunk_3741
import Theorems.Thm_Brocard_berndt_galway_chunk_3742
import Theorems.Thm_Brocard_berndt_galway_chunk_3743
import Theorems.Thm_Brocard_berndt_galway_chunk_3744
import Theorems.Thm_Brocard_berndt_galway_chunk_3745
import Theorems.Thm_Brocard_berndt_galway_chunk_3746
import Theorems.Thm_Brocard_berndt_galway_chunk_3747
import Theorems.Thm_Brocard_berndt_galway_chunk_3748
import Theorems.Thm_Brocard_berndt_galway_chunk_3749
import Theorems.Thm_Brocard_berndt_galway_chunk_3750
import Theorems.Thm_Brocard_berndt_galway_chunk_3751
import Theorems.Thm_Brocard_berndt_galway_chunk_3752
import Theorems.Thm_Brocard_berndt_galway_chunk_3753
import Theorems.Thm_Brocard_berndt_galway_chunk_3754

theorem solution (n m : ℕ) (h1 : 666906474 ≤ n) (h2 : n < 675179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 671043165 with hs0 | hs0
  · -- n < 671043165
    rcases Nat.lt_or_ge n 669064748 with hs1 | hs1
    · -- n < 669064748
      rcases Nat.lt_or_ge n 667985611 with hs2 | hs2
      · -- n < 667985611
        rcases Nat.lt_or_ge n 667446043 with hs3 | hs3
        · -- n < 667446043
          rcases Nat.lt_or_ge n 667266187 with hs4 | hs4
          · -- n < 667266187
            rcases Nat.lt_or_ge n 667086330 with hs5 | hs5
            · -- n < 667086330
              exact Brocard.berndt_galway_chunk_3709 n m (by omega) (by omega) h
            · -- n >= 667086330
              exact Brocard.berndt_galway_chunk_3710 n m (by omega) (by omega) h
          · -- n >= 667266187
            exact Brocard.berndt_galway_chunk_3711 n m (by omega) (by omega) h
        · -- n >= 667446043
          rcases Nat.lt_or_ge n 667805755 with hs4 | hs4
          · -- n < 667805755
            rcases Nat.lt_or_ge n 667625899 with hs5 | hs5
            · -- n < 667625899
              exact Brocard.berndt_galway_chunk_3712 n m (by omega) (by omega) h
            · -- n >= 667625899
              exact Brocard.berndt_galway_chunk_3713 n m (by omega) (by omega) h
          · -- n >= 667805755
            exact Brocard.berndt_galway_chunk_3714 n m (by omega) (by omega) h
      · -- n >= 667985611
        rcases Nat.lt_or_ge n 668525179 with hs3 | hs3
        · -- n < 668525179
          rcases Nat.lt_or_ge n 668345323 with hs4 | hs4
          · -- n < 668345323
            rcases Nat.lt_or_ge n 668165467 with hs5 | hs5
            · -- n < 668165467
              exact Brocard.berndt_galway_chunk_3715 n m (by omega) (by omega) h
            · -- n >= 668165467
              exact Brocard.berndt_galway_chunk_3716 n m (by omega) (by omega) h
          · -- n >= 668345323
            exact Brocard.berndt_galway_chunk_3717 n m (by omega) (by omega) h
        · -- n >= 668525179
          rcases Nat.lt_or_ge n 668884892 with hs4 | hs4
          · -- n < 668884892
            rcases Nat.lt_or_ge n 668705035 with hs5 | hs5
            · -- n < 668705035
              exact Brocard.berndt_galway_chunk_3718 n m (by omega) (by omega) h
            · -- n >= 668705035
              exact Brocard.berndt_galway_chunk_3719 n m (by omega) (by omega) h
          · -- n >= 668884892
            exact Brocard.berndt_galway_chunk_3720 n m (by omega) (by omega) h
    · -- n >= 669064748
      rcases Nat.lt_or_ge n 670143884 with hs2 | hs2
      · -- n < 670143884
        rcases Nat.lt_or_ge n 669604316 with hs3 | hs3
        · -- n < 669604316
          rcases Nat.lt_or_ge n 669424460 with hs4 | hs4
          · -- n < 669424460
            rcases Nat.lt_or_ge n 669244604 with hs5 | hs5
            · -- n < 669244604
              exact Brocard.berndt_galway_chunk_3721 n m (by omega) (by omega) h
            · -- n >= 669244604
              exact Brocard.berndt_galway_chunk_3722 n m (by omega) (by omega) h
          · -- n >= 669424460
            exact Brocard.berndt_galway_chunk_3723 n m (by omega) (by omega) h
        · -- n >= 669604316
          rcases Nat.lt_or_ge n 669964028 with hs4 | hs4
          · -- n < 669964028
            rcases Nat.lt_or_ge n 669784172 with hs5 | hs5
            · -- n < 669784172
              exact Brocard.berndt_galway_chunk_3724 n m (by omega) (by omega) h
            · -- n >= 669784172
              exact Brocard.berndt_galway_chunk_3725 n m (by omega) (by omega) h
          · -- n >= 669964028
            exact Brocard.berndt_galway_chunk_3726 n m (by omega) (by omega) h
      · -- n >= 670143884
        rcases Nat.lt_or_ge n 670683453 with hs3 | hs3
        · -- n < 670683453
          rcases Nat.lt_or_ge n 670503597 with hs4 | hs4
          · -- n < 670503597
            rcases Nat.lt_or_ge n 670323741 with hs5 | hs5
            · -- n < 670323741
              exact Brocard.berndt_galway_chunk_3727 n m (by omega) (by omega) h
            · -- n >= 670323741
              exact Brocard.berndt_galway_chunk_3728 n m (by omega) (by omega) h
          · -- n >= 670503597
            exact Brocard.berndt_galway_chunk_3729 n m (by omega) (by omega) h
        · -- n >= 670683453
          rcases Nat.lt_or_ge n 670863309 with hs4 | hs4
          · -- n < 670863309
            exact Brocard.berndt_galway_chunk_3730 n m (by omega) (by omega) h
          · -- n >= 670863309
            exact Brocard.berndt_galway_chunk_3731 n m (by omega) (by omega) h
  · -- n >= 671043165
    rcases Nat.lt_or_ge n 673201438 with hs1 | hs1
    · -- n < 673201438
      rcases Nat.lt_or_ge n 672122302 with hs2 | hs2
      · -- n < 672122302
        rcases Nat.lt_or_ge n 671582733 with hs3 | hs3
        · -- n < 671582733
          rcases Nat.lt_or_ge n 671402877 with hs4 | hs4
          · -- n < 671402877
            rcases Nat.lt_or_ge n 671223021 with hs5 | hs5
            · -- n < 671223021
              exact Brocard.berndt_galway_chunk_3732 n m (by omega) (by omega) h
            · -- n >= 671223021
              exact Brocard.berndt_galway_chunk_3733 n m (by omega) (by omega) h
          · -- n >= 671402877
            exact Brocard.berndt_galway_chunk_3734 n m (by omega) (by omega) h
        · -- n >= 671582733
          rcases Nat.lt_or_ge n 671942446 with hs4 | hs4
          · -- n < 671942446
            rcases Nat.lt_or_ge n 671762589 with hs5 | hs5
            · -- n < 671762589
              exact Brocard.berndt_galway_chunk_3735 n m (by omega) (by omega) h
            · -- n >= 671762589
              exact Brocard.berndt_galway_chunk_3736 n m (by omega) (by omega) h
          · -- n >= 671942446
            exact Brocard.berndt_galway_chunk_3737 n m (by omega) (by omega) h
      · -- n >= 672122302
        rcases Nat.lt_or_ge n 672661870 with hs3 | hs3
        · -- n < 672661870
          rcases Nat.lt_or_ge n 672482014 with hs4 | hs4
          · -- n < 672482014
            rcases Nat.lt_or_ge n 672302158 with hs5 | hs5
            · -- n < 672302158
              exact Brocard.berndt_galway_chunk_3738 n m (by omega) (by omega) h
            · -- n >= 672302158
              exact Brocard.berndt_galway_chunk_3739 n m (by omega) (by omega) h
          · -- n >= 672482014
            exact Brocard.berndt_galway_chunk_3740 n m (by omega) (by omega) h
        · -- n >= 672661870
          rcases Nat.lt_or_ge n 673021582 with hs4 | hs4
          · -- n < 673021582
            rcases Nat.lt_or_ge n 672841726 with hs5 | hs5
            · -- n < 672841726
              exact Brocard.berndt_galway_chunk_3741 n m (by omega) (by omega) h
            · -- n >= 672841726
              exact Brocard.berndt_galway_chunk_3742 n m (by omega) (by omega) h
          · -- n >= 673021582
            exact Brocard.berndt_galway_chunk_3743 n m (by omega) (by omega) h
    · -- n >= 673201438
      rcases Nat.lt_or_ge n 674280575 with hs2 | hs2
      · -- n < 674280575
        rcases Nat.lt_or_ge n 673741007 with hs3 | hs3
        · -- n < 673741007
          rcases Nat.lt_or_ge n 673561151 with hs4 | hs4
          · -- n < 673561151
            rcases Nat.lt_or_ge n 673381294 with hs5 | hs5
            · -- n < 673381294
              exact Brocard.berndt_galway_chunk_3744 n m (by omega) (by omega) h
            · -- n >= 673381294
              exact Brocard.berndt_galway_chunk_3745 n m (by omega) (by omega) h
          · -- n >= 673561151
            exact Brocard.berndt_galway_chunk_3746 n m (by omega) (by omega) h
        · -- n >= 673741007
          rcases Nat.lt_or_ge n 674100719 with hs4 | hs4
          · -- n < 674100719
            rcases Nat.lt_or_ge n 673920863 with hs5 | hs5
            · -- n < 673920863
              exact Brocard.berndt_galway_chunk_3747 n m (by omega) (by omega) h
            · -- n >= 673920863
              exact Brocard.berndt_galway_chunk_3748 n m (by omega) (by omega) h
          · -- n >= 674100719
            exact Brocard.berndt_galway_chunk_3749 n m (by omega) (by omega) h
      · -- n >= 674280575
        rcases Nat.lt_or_ge n 674820143 with hs3 | hs3
        · -- n < 674820143
          rcases Nat.lt_or_ge n 674640287 with hs4 | hs4
          · -- n < 674640287
            rcases Nat.lt_or_ge n 674460431 with hs5 | hs5
            · -- n < 674460431
              exact Brocard.berndt_galway_chunk_3750 n m (by omega) (by omega) h
            · -- n >= 674460431
              exact Brocard.berndt_galway_chunk_3751 n m (by omega) (by omega) h
          · -- n >= 674640287
            exact Brocard.berndt_galway_chunk_3752 n m (by omega) (by omega) h
        · -- n >= 674820143
          rcases Nat.lt_or_ge n 675000000 with hs4 | hs4
          · -- n < 675000000
            exact Brocard.berndt_galway_chunk_3753 n m (by omega) (by omega) h
          · -- n >= 675000000
            exact Brocard.berndt_galway_chunk_3754 n m (by omega) (by omega) h
