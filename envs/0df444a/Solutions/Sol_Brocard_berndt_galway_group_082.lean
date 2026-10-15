-- Prove2me | solution 1 for Brocard.berndt_galway_group_082
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:50:12.1314+00:00
-- url     : https://prove2.me/submissions/73191d7c-d461-4ee1-88f8-2652fa74ebfe

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_3755
import Theorems.Thm_Brocard_berndt_galway_chunk_3756
import Theorems.Thm_Brocard_berndt_galway_chunk_3757
import Theorems.Thm_Brocard_berndt_galway_chunk_3758
import Theorems.Thm_Brocard_berndt_galway_chunk_3759
import Theorems.Thm_Brocard_berndt_galway_chunk_3760
import Theorems.Thm_Brocard_berndt_galway_chunk_3761
import Theorems.Thm_Brocard_berndt_galway_chunk_3762
import Theorems.Thm_Brocard_berndt_galway_chunk_3763
import Theorems.Thm_Brocard_berndt_galway_chunk_3764
import Theorems.Thm_Brocard_berndt_galway_chunk_3765
import Theorems.Thm_Brocard_berndt_galway_chunk_3766
import Theorems.Thm_Brocard_berndt_galway_chunk_3767
import Theorems.Thm_Brocard_berndt_galway_chunk_3768
import Theorems.Thm_Brocard_berndt_galway_chunk_3769
import Theorems.Thm_Brocard_berndt_galway_chunk_3770
import Theorems.Thm_Brocard_berndt_galway_chunk_3771
import Theorems.Thm_Brocard_berndt_galway_chunk_3772
import Theorems.Thm_Brocard_berndt_galway_chunk_3773
import Theorems.Thm_Brocard_berndt_galway_chunk_3774
import Theorems.Thm_Brocard_berndt_galway_chunk_3775
import Theorems.Thm_Brocard_berndt_galway_chunk_3776
import Theorems.Thm_Brocard_berndt_galway_chunk_3777
import Theorems.Thm_Brocard_berndt_galway_chunk_3778
import Theorems.Thm_Brocard_berndt_galway_chunk_3779
import Theorems.Thm_Brocard_berndt_galway_chunk_3780
import Theorems.Thm_Brocard_berndt_galway_chunk_3781
import Theorems.Thm_Brocard_berndt_galway_chunk_3782
import Theorems.Thm_Brocard_berndt_galway_chunk_3783
import Theorems.Thm_Brocard_berndt_galway_chunk_3784
import Theorems.Thm_Brocard_berndt_galway_chunk_3785
import Theorems.Thm_Brocard_berndt_galway_chunk_3786
import Theorems.Thm_Brocard_berndt_galway_chunk_3787
import Theorems.Thm_Brocard_berndt_galway_chunk_3788
import Theorems.Thm_Brocard_berndt_galway_chunk_3789
import Theorems.Thm_Brocard_berndt_galway_chunk_3790
import Theorems.Thm_Brocard_berndt_galway_chunk_3791
import Theorems.Thm_Brocard_berndt_galway_chunk_3792
import Theorems.Thm_Brocard_berndt_galway_chunk_3793
import Theorems.Thm_Brocard_berndt_galway_chunk_3794
import Theorems.Thm_Brocard_berndt_galway_chunk_3795
import Theorems.Thm_Brocard_berndt_galway_chunk_3796
import Theorems.Thm_Brocard_berndt_galway_chunk_3797
import Theorems.Thm_Brocard_berndt_galway_chunk_3798
import Theorems.Thm_Brocard_berndt_galway_chunk_3799
import Theorems.Thm_Brocard_berndt_galway_chunk_3800

theorem solution (n m : ℕ) (h1 : 675179856 ≤ n) (h2 : n < 683453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 679316546 with hs0 | hs0
  · -- n < 679316546
    rcases Nat.lt_or_ge n 677338129 with hs1 | hs1
    · -- n < 677338129
      rcases Nat.lt_or_ge n 676258992 with hs2 | hs2
      · -- n < 676258992
        rcases Nat.lt_or_ge n 675719424 with hs3 | hs3
        · -- n < 675719424
          rcases Nat.lt_or_ge n 675539568 with hs4 | hs4
          · -- n < 675539568
            rcases Nat.lt_or_ge n 675359712 with hs5 | hs5
            · -- n < 675359712
              exact Brocard.berndt_galway_chunk_3755 n m (by omega) (by omega) h
            · -- n >= 675359712
              exact Brocard.berndt_galway_chunk_3756 n m (by omega) (by omega) h
          · -- n >= 675539568
            exact Brocard.berndt_galway_chunk_3757 n m (by omega) (by omega) h
        · -- n >= 675719424
          rcases Nat.lt_or_ge n 676079136 with hs4 | hs4
          · -- n < 676079136
            rcases Nat.lt_or_ge n 675899280 with hs5 | hs5
            · -- n < 675899280
              exact Brocard.berndt_galway_chunk_3758 n m (by omega) (by omega) h
            · -- n >= 675899280
              exact Brocard.berndt_galway_chunk_3759 n m (by omega) (by omega) h
          · -- n >= 676079136
            exact Brocard.berndt_galway_chunk_3760 n m (by omega) (by omega) h
      · -- n >= 676258992
        rcases Nat.lt_or_ge n 676798561 with hs3 | hs3
        · -- n < 676798561
          rcases Nat.lt_or_ge n 676618705 with hs4 | hs4
          · -- n < 676618705
            rcases Nat.lt_or_ge n 676438848 with hs5 | hs5
            · -- n < 676438848
              exact Brocard.berndt_galway_chunk_3761 n m (by omega) (by omega) h
            · -- n >= 676438848
              exact Brocard.berndt_galway_chunk_3762 n m (by omega) (by omega) h
          · -- n >= 676618705
            exact Brocard.berndt_galway_chunk_3763 n m (by omega) (by omega) h
        · -- n >= 676798561
          rcases Nat.lt_or_ge n 677158273 with hs4 | hs4
          · -- n < 677158273
            rcases Nat.lt_or_ge n 676978417 with hs5 | hs5
            · -- n < 676978417
              exact Brocard.berndt_galway_chunk_3764 n m (by omega) (by omega) h
            · -- n >= 676978417
              exact Brocard.berndt_galway_chunk_3765 n m (by omega) (by omega) h
          · -- n >= 677158273
            exact Brocard.berndt_galway_chunk_3766 n m (by omega) (by omega) h
    · -- n >= 677338129
      rcases Nat.lt_or_ge n 678417266 with hs2 | hs2
      · -- n < 678417266
        rcases Nat.lt_or_ge n 677877697 with hs3 | hs3
        · -- n < 677877697
          rcases Nat.lt_or_ge n 677697841 with hs4 | hs4
          · -- n < 677697841
            rcases Nat.lt_or_ge n 677517985 with hs5 | hs5
            · -- n < 677517985
              exact Brocard.berndt_galway_chunk_3767 n m (by omega) (by omega) h
            · -- n >= 677517985
              exact Brocard.berndt_galway_chunk_3768 n m (by omega) (by omega) h
          · -- n >= 677697841
            exact Brocard.berndt_galway_chunk_3769 n m (by omega) (by omega) h
        · -- n >= 677877697
          rcases Nat.lt_or_ge n 678237410 with hs4 | hs4
          · -- n < 678237410
            rcases Nat.lt_or_ge n 678057553 with hs5 | hs5
            · -- n < 678057553
              exact Brocard.berndt_galway_chunk_3770 n m (by omega) (by omega) h
            · -- n >= 678057553
              exact Brocard.berndt_galway_chunk_3771 n m (by omega) (by omega) h
          · -- n >= 678237410
            exact Brocard.berndt_galway_chunk_3772 n m (by omega) (by omega) h
      · -- n >= 678417266
        rcases Nat.lt_or_ge n 678956834 with hs3 | hs3
        · -- n < 678956834
          rcases Nat.lt_or_ge n 678776978 with hs4 | hs4
          · -- n < 678776978
            rcases Nat.lt_or_ge n 678597122 with hs5 | hs5
            · -- n < 678597122
              exact Brocard.berndt_galway_chunk_3773 n m (by omega) (by omega) h
            · -- n >= 678597122
              exact Brocard.berndt_galway_chunk_3774 n m (by omega) (by omega) h
          · -- n >= 678776978
            exact Brocard.berndt_galway_chunk_3775 n m (by omega) (by omega) h
        · -- n >= 678956834
          rcases Nat.lt_or_ge n 679136690 with hs4 | hs4
          · -- n < 679136690
            exact Brocard.berndt_galway_chunk_3776 n m (by omega) (by omega) h
          · -- n >= 679136690
            exact Brocard.berndt_galway_chunk_3777 n m (by omega) (by omega) h
  · -- n >= 679316546
    rcases Nat.lt_or_ge n 681474820 with hs1 | hs1
    · -- n < 681474820
      rcases Nat.lt_or_ge n 680395683 with hs2 | hs2
      · -- n < 680395683
        rcases Nat.lt_or_ge n 679856115 with hs3 | hs3
        · -- n < 679856115
          rcases Nat.lt_or_ge n 679676258 with hs4 | hs4
          · -- n < 679676258
            rcases Nat.lt_or_ge n 679496402 with hs5 | hs5
            · -- n < 679496402
              exact Brocard.berndt_galway_chunk_3778 n m (by omega) (by omega) h
            · -- n >= 679496402
              exact Brocard.berndt_galway_chunk_3779 n m (by omega) (by omega) h
          · -- n >= 679676258
            exact Brocard.berndt_galway_chunk_3780 n m (by omega) (by omega) h
        · -- n >= 679856115
          rcases Nat.lt_or_ge n 680215827 with hs4 | hs4
          · -- n < 680215827
            rcases Nat.lt_or_ge n 680035971 with hs5 | hs5
            · -- n < 680035971
              exact Brocard.berndt_galway_chunk_3781 n m (by omega) (by omega) h
            · -- n >= 680035971
              exact Brocard.berndt_galway_chunk_3782 n m (by omega) (by omega) h
          · -- n >= 680215827
            exact Brocard.berndt_galway_chunk_3783 n m (by omega) (by omega) h
      · -- n >= 680395683
        rcases Nat.lt_or_ge n 680935251 with hs3 | hs3
        · -- n < 680935251
          rcases Nat.lt_or_ge n 680755395 with hs4 | hs4
          · -- n < 680755395
            rcases Nat.lt_or_ge n 680575539 with hs5 | hs5
            · -- n < 680575539
              exact Brocard.berndt_galway_chunk_3784 n m (by omega) (by omega) h
            · -- n >= 680575539
              exact Brocard.berndt_galway_chunk_3785 n m (by omega) (by omega) h
          · -- n >= 680755395
            exact Brocard.berndt_galway_chunk_3786 n m (by omega) (by omega) h
        · -- n >= 680935251
          rcases Nat.lt_or_ge n 681294964 with hs4 | hs4
          · -- n < 681294964
            rcases Nat.lt_or_ge n 681115107 with hs5 | hs5
            · -- n < 681115107
              exact Brocard.berndt_galway_chunk_3787 n m (by omega) (by omega) h
            · -- n >= 681115107
              exact Brocard.berndt_galway_chunk_3788 n m (by omega) (by omega) h
          · -- n >= 681294964
            exact Brocard.berndt_galway_chunk_3789 n m (by omega) (by omega) h
    · -- n >= 681474820
      rcases Nat.lt_or_ge n 682553956 with hs2 | hs2
      · -- n < 682553956
        rcases Nat.lt_or_ge n 682014388 with hs3 | hs3
        · -- n < 682014388
          rcases Nat.lt_or_ge n 681834532 with hs4 | hs4
          · -- n < 681834532
            rcases Nat.lt_or_ge n 681654676 with hs5 | hs5
            · -- n < 681654676
              exact Brocard.berndt_galway_chunk_3790 n m (by omega) (by omega) h
            · -- n >= 681654676
              exact Brocard.berndt_galway_chunk_3791 n m (by omega) (by omega) h
          · -- n >= 681834532
            exact Brocard.berndt_galway_chunk_3792 n m (by omega) (by omega) h
        · -- n >= 682014388
          rcases Nat.lt_or_ge n 682374100 with hs4 | hs4
          · -- n < 682374100
            rcases Nat.lt_or_ge n 682194244 with hs5 | hs5
            · -- n < 682194244
              exact Brocard.berndt_galway_chunk_3793 n m (by omega) (by omega) h
            · -- n >= 682194244
              exact Brocard.berndt_galway_chunk_3794 n m (by omega) (by omega) h
          · -- n >= 682374100
            exact Brocard.berndt_galway_chunk_3795 n m (by omega) (by omega) h
      · -- n >= 682553956
        rcases Nat.lt_or_ge n 683093525 with hs3 | hs3
        · -- n < 683093525
          rcases Nat.lt_or_ge n 682913669 with hs4 | hs4
          · -- n < 682913669
            rcases Nat.lt_or_ge n 682733812 with hs5 | hs5
            · -- n < 682733812
              exact Brocard.berndt_galway_chunk_3796 n m (by omega) (by omega) h
            · -- n >= 682733812
              exact Brocard.berndt_galway_chunk_3797 n m (by omega) (by omega) h
          · -- n >= 682913669
            exact Brocard.berndt_galway_chunk_3798 n m (by omega) (by omega) h
        · -- n >= 683093525
          rcases Nat.lt_or_ge n 683273381 with hs4 | hs4
          · -- n < 683273381
            exact Brocard.berndt_galway_chunk_3799 n m (by omega) (by omega) h
          · -- n >= 683273381
            exact Brocard.berndt_galway_chunk_3800 n m (by omega) (by omega) h
