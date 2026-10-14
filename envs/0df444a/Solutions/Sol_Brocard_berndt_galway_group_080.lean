-- Prove2me | solution 1 for Brocard.berndt_galway_group_080
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:31:47.944809+00:00
-- url     : https://prove2.me/submissions/ef645634-d68d-4643-bbb6-22e1e4483ada

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_3663
import Theorems.Thm_Brocard_berndt_galway_chunk_3664
import Theorems.Thm_Brocard_berndt_galway_chunk_3665
import Theorems.Thm_Brocard_berndt_galway_chunk_3666
import Theorems.Thm_Brocard_berndt_galway_chunk_3667
import Theorems.Thm_Brocard_berndt_galway_chunk_3668
import Theorems.Thm_Brocard_berndt_galway_chunk_3669
import Theorems.Thm_Brocard_berndt_galway_chunk_3670
import Theorems.Thm_Brocard_berndt_galway_chunk_3671
import Theorems.Thm_Brocard_berndt_galway_chunk_3672
import Theorems.Thm_Brocard_berndt_galway_chunk_3673
import Theorems.Thm_Brocard_berndt_galway_chunk_3674
import Theorems.Thm_Brocard_berndt_galway_chunk_3675
import Theorems.Thm_Brocard_berndt_galway_chunk_3676
import Theorems.Thm_Brocard_berndt_galway_chunk_3677
import Theorems.Thm_Brocard_berndt_galway_chunk_3678
import Theorems.Thm_Brocard_berndt_galway_chunk_3679
import Theorems.Thm_Brocard_berndt_galway_chunk_3680
import Theorems.Thm_Brocard_berndt_galway_chunk_3681
import Theorems.Thm_Brocard_berndt_galway_chunk_3682
import Theorems.Thm_Brocard_berndt_galway_chunk_3683
import Theorems.Thm_Brocard_berndt_galway_chunk_3684
import Theorems.Thm_Brocard_berndt_galway_chunk_3685
import Theorems.Thm_Brocard_berndt_galway_chunk_3686
import Theorems.Thm_Brocard_berndt_galway_chunk_3687
import Theorems.Thm_Brocard_berndt_galway_chunk_3688
import Theorems.Thm_Brocard_berndt_galway_chunk_3689
import Theorems.Thm_Brocard_berndt_galway_chunk_3690
import Theorems.Thm_Brocard_berndt_galway_chunk_3691
import Theorems.Thm_Brocard_berndt_galway_chunk_3692
import Theorems.Thm_Brocard_berndt_galway_chunk_3693
import Theorems.Thm_Brocard_berndt_galway_chunk_3694
import Theorems.Thm_Brocard_berndt_galway_chunk_3695
import Theorems.Thm_Brocard_berndt_galway_chunk_3696
import Theorems.Thm_Brocard_berndt_galway_chunk_3697
import Theorems.Thm_Brocard_berndt_galway_chunk_3698
import Theorems.Thm_Brocard_berndt_galway_chunk_3699
import Theorems.Thm_Brocard_berndt_galway_chunk_3700
import Theorems.Thm_Brocard_berndt_galway_chunk_3701
import Theorems.Thm_Brocard_berndt_galway_chunk_3702
import Theorems.Thm_Brocard_berndt_galway_chunk_3703
import Theorems.Thm_Brocard_berndt_galway_chunk_3704
import Theorems.Thm_Brocard_berndt_galway_chunk_3705
import Theorems.Thm_Brocard_berndt_galway_chunk_3706
import Theorems.Thm_Brocard_berndt_galway_chunk_3707
import Theorems.Thm_Brocard_berndt_galway_chunk_3708

theorem solution (n m : ℕ) (h1 : 658633093 ≤ n) (h2 : n < 666906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 662769784 with hs0 | hs0
  · -- n < 662769784
    rcases Nat.lt_or_ge n 660791366 with hs1 | hs1
    · -- n < 660791366
      rcases Nat.lt_or_ge n 659712230 with hs2 | hs2
      · -- n < 659712230
        rcases Nat.lt_or_ge n 659172661 with hs3 | hs3
        · -- n < 659172661
          rcases Nat.lt_or_ge n 658992805 with hs4 | hs4
          · -- n < 658992805
            rcases Nat.lt_or_ge n 658812949 with hs5 | hs5
            · -- n < 658812949
              exact Brocard.berndt_galway_chunk_3663 n m (by omega) (by omega) h
            · -- n >= 658812949
              exact Brocard.berndt_galway_chunk_3664 n m (by omega) (by omega) h
          · -- n >= 658992805
            exact Brocard.berndt_galway_chunk_3665 n m (by omega) (by omega) h
        · -- n >= 659172661
          rcases Nat.lt_or_ge n 659532374 with hs4 | hs4
          · -- n < 659532374
            rcases Nat.lt_or_ge n 659352517 with hs5 | hs5
            · -- n < 659352517
              exact Brocard.berndt_galway_chunk_3666 n m (by omega) (by omega) h
            · -- n >= 659352517
              exact Brocard.berndt_galway_chunk_3667 n m (by omega) (by omega) h
          · -- n >= 659532374
            exact Brocard.berndt_galway_chunk_3668 n m (by omega) (by omega) h
      · -- n >= 659712230
        rcases Nat.lt_or_ge n 660251798 with hs3 | hs3
        · -- n < 660251798
          rcases Nat.lt_or_ge n 660071942 with hs4 | hs4
          · -- n < 660071942
            rcases Nat.lt_or_ge n 659892086 with hs5 | hs5
            · -- n < 659892086
              exact Brocard.berndt_galway_chunk_3669 n m (by omega) (by omega) h
            · -- n >= 659892086
              exact Brocard.berndt_galway_chunk_3670 n m (by omega) (by omega) h
          · -- n >= 660071942
            exact Brocard.berndt_galway_chunk_3671 n m (by omega) (by omega) h
        · -- n >= 660251798
          rcases Nat.lt_or_ge n 660611510 with hs4 | hs4
          · -- n < 660611510
            rcases Nat.lt_or_ge n 660431654 with hs5 | hs5
            · -- n < 660431654
              exact Brocard.berndt_galway_chunk_3672 n m (by omega) (by omega) h
            · -- n >= 660431654
              exact Brocard.berndt_galway_chunk_3673 n m (by omega) (by omega) h
          · -- n >= 660611510
            exact Brocard.berndt_galway_chunk_3674 n m (by omega) (by omega) h
    · -- n >= 660791366
      rcases Nat.lt_or_ge n 661870503 with hs2 | hs2
      · -- n < 661870503
        rcases Nat.lt_or_ge n 661330935 with hs3 | hs3
        · -- n < 661330935
          rcases Nat.lt_or_ge n 661151079 with hs4 | hs4
          · -- n < 661151079
            rcases Nat.lt_or_ge n 660971223 with hs5 | hs5
            · -- n < 660971223
              exact Brocard.berndt_galway_chunk_3675 n m (by omega) (by omega) h
            · -- n >= 660971223
              exact Brocard.berndt_galway_chunk_3676 n m (by omega) (by omega) h
          · -- n >= 661151079
            exact Brocard.berndt_galway_chunk_3677 n m (by omega) (by omega) h
        · -- n >= 661330935
          rcases Nat.lt_or_ge n 661690647 with hs4 | hs4
          · -- n < 661690647
            rcases Nat.lt_or_ge n 661510791 with hs5 | hs5
            · -- n < 661510791
              exact Brocard.berndt_galway_chunk_3678 n m (by omega) (by omega) h
            · -- n >= 661510791
              exact Brocard.berndt_galway_chunk_3679 n m (by omega) (by omega) h
          · -- n >= 661690647
            exact Brocard.berndt_galway_chunk_3680 n m (by omega) (by omega) h
      · -- n >= 661870503
        rcases Nat.lt_or_ge n 662410071 with hs3 | hs3
        · -- n < 662410071
          rcases Nat.lt_or_ge n 662230215 with hs4 | hs4
          · -- n < 662230215
            rcases Nat.lt_or_ge n 662050359 with hs5 | hs5
            · -- n < 662050359
              exact Brocard.berndt_galway_chunk_3681 n m (by omega) (by omega) h
            · -- n >= 662050359
              exact Brocard.berndt_galway_chunk_3682 n m (by omega) (by omega) h
          · -- n >= 662230215
            exact Brocard.berndt_galway_chunk_3683 n m (by omega) (by omega) h
        · -- n >= 662410071
          rcases Nat.lt_or_ge n 662589928 with hs4 | hs4
          · -- n < 662589928
            exact Brocard.berndt_galway_chunk_3684 n m (by omega) (by omega) h
          · -- n >= 662589928
            exact Brocard.berndt_galway_chunk_3685 n m (by omega) (by omega) h
  · -- n >= 662769784
    rcases Nat.lt_or_ge n 664928057 with hs1 | hs1
    · -- n < 664928057
      rcases Nat.lt_or_ge n 663848920 with hs2 | hs2
      · -- n < 663848920
        rcases Nat.lt_or_ge n 663309352 with hs3 | hs3
        · -- n < 663309352
          rcases Nat.lt_or_ge n 663129496 with hs4 | hs4
          · -- n < 663129496
            rcases Nat.lt_or_ge n 662949640 with hs5 | hs5
            · -- n < 662949640
              exact Brocard.berndt_galway_chunk_3686 n m (by omega) (by omega) h
            · -- n >= 662949640
              exact Brocard.berndt_galway_chunk_3687 n m (by omega) (by omega) h
          · -- n >= 663129496
            exact Brocard.berndt_galway_chunk_3688 n m (by omega) (by omega) h
        · -- n >= 663309352
          rcases Nat.lt_or_ge n 663669064 with hs4 | hs4
          · -- n < 663669064
            rcases Nat.lt_or_ge n 663489208 with hs5 | hs5
            · -- n < 663489208
              exact Brocard.berndt_galway_chunk_3689 n m (by omega) (by omega) h
            · -- n >= 663489208
              exact Brocard.berndt_galway_chunk_3690 n m (by omega) (by omega) h
          · -- n >= 663669064
            exact Brocard.berndt_galway_chunk_3691 n m (by omega) (by omega) h
      · -- n >= 663848920
        rcases Nat.lt_or_ge n 664388489 with hs3 | hs3
        · -- n < 664388489
          rcases Nat.lt_or_ge n 664208633 with hs4 | hs4
          · -- n < 664208633
            rcases Nat.lt_or_ge n 664028776 with hs5 | hs5
            · -- n < 664028776
              exact Brocard.berndt_galway_chunk_3692 n m (by omega) (by omega) h
            · -- n >= 664028776
              exact Brocard.berndt_galway_chunk_3693 n m (by omega) (by omega) h
          · -- n >= 664208633
            exact Brocard.berndt_galway_chunk_3694 n m (by omega) (by omega) h
        · -- n >= 664388489
          rcases Nat.lt_or_ge n 664748201 with hs4 | hs4
          · -- n < 664748201
            rcases Nat.lt_or_ge n 664568345 with hs5 | hs5
            · -- n < 664568345
              exact Brocard.berndt_galway_chunk_3695 n m (by omega) (by omega) h
            · -- n >= 664568345
              exact Brocard.berndt_galway_chunk_3696 n m (by omega) (by omega) h
          · -- n >= 664748201
            exact Brocard.berndt_galway_chunk_3697 n m (by omega) (by omega) h
    · -- n >= 664928057
      rcases Nat.lt_or_ge n 666007194 with hs2 | hs2
      · -- n < 666007194
        rcases Nat.lt_or_ge n 665467625 with hs3 | hs3
        · -- n < 665467625
          rcases Nat.lt_or_ge n 665287769 with hs4 | hs4
          · -- n < 665287769
            rcases Nat.lt_or_ge n 665107913 with hs5 | hs5
            · -- n < 665107913
              exact Brocard.berndt_galway_chunk_3698 n m (by omega) (by omega) h
            · -- n >= 665107913
              exact Brocard.berndt_galway_chunk_3699 n m (by omega) (by omega) h
          · -- n >= 665287769
            exact Brocard.berndt_galway_chunk_3700 n m (by omega) (by omega) h
        · -- n >= 665467625
          rcases Nat.lt_or_ge n 665827338 with hs4 | hs4
          · -- n < 665827338
            rcases Nat.lt_or_ge n 665647482 with hs5 | hs5
            · -- n < 665647482
              exact Brocard.berndt_galway_chunk_3701 n m (by omega) (by omega) h
            · -- n >= 665647482
              exact Brocard.berndt_galway_chunk_3702 n m (by omega) (by omega) h
          · -- n >= 665827338
            exact Brocard.berndt_galway_chunk_3703 n m (by omega) (by omega) h
      · -- n >= 666007194
        rcases Nat.lt_or_ge n 666546762 with hs3 | hs3
        · -- n < 666546762
          rcases Nat.lt_or_ge n 666366906 with hs4 | hs4
          · -- n < 666366906
            rcases Nat.lt_or_ge n 666187050 with hs5 | hs5
            · -- n < 666187050
              exact Brocard.berndt_galway_chunk_3704 n m (by omega) (by omega) h
            · -- n >= 666187050
              exact Brocard.berndt_galway_chunk_3705 n m (by omega) (by omega) h
          · -- n >= 666366906
            exact Brocard.berndt_galway_chunk_3706 n m (by omega) (by omega) h
        · -- n >= 666546762
          rcases Nat.lt_or_ge n 666726618 with hs4 | hs4
          · -- n < 666726618
            exact Brocard.berndt_galway_chunk_3707 n m (by omega) (by omega) h
          · -- n >= 666726618
            exact Brocard.berndt_galway_chunk_3708 n m (by omega) (by omega) h
