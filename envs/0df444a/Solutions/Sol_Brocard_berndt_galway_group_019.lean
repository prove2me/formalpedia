-- Prove2me | solution 1 for Brocard.berndt_galway_group_019
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:41:51.964205+00:00
-- url     : https://prove2.me/submissions/0d7e3a1f-981e-4905-9996-1872114f0f4e

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_0837
import Theorems.Thm_Brocard_berndt_galway_chunk_0838
import Theorems.Thm_Brocard_berndt_galway_chunk_0839
import Theorems.Thm_Brocard_berndt_galway_chunk_0840
import Theorems.Thm_Brocard_berndt_galway_chunk_0841
import Theorems.Thm_Brocard_berndt_galway_chunk_0842
import Theorems.Thm_Brocard_berndt_galway_chunk_0843
import Theorems.Thm_Brocard_berndt_galway_chunk_0844
import Theorems.Thm_Brocard_berndt_galway_chunk_0845
import Theorems.Thm_Brocard_berndt_galway_chunk_0846
import Theorems.Thm_Brocard_berndt_galway_chunk_0847
import Theorems.Thm_Brocard_berndt_galway_chunk_0848
import Theorems.Thm_Brocard_berndt_galway_chunk_0849
import Theorems.Thm_Brocard_berndt_galway_chunk_0850
import Theorems.Thm_Brocard_berndt_galway_chunk_0851
import Theorems.Thm_Brocard_berndt_galway_chunk_0852
import Theorems.Thm_Brocard_berndt_galway_chunk_0853
import Theorems.Thm_Brocard_berndt_galway_chunk_0854
import Theorems.Thm_Brocard_berndt_galway_chunk_0855
import Theorems.Thm_Brocard_berndt_galway_chunk_0856
import Theorems.Thm_Brocard_berndt_galway_chunk_0857
import Theorems.Thm_Brocard_berndt_galway_chunk_0858
import Theorems.Thm_Brocard_berndt_galway_chunk_0859
import Theorems.Thm_Brocard_berndt_galway_chunk_0860
import Theorems.Thm_Brocard_berndt_galway_chunk_0861
import Theorems.Thm_Brocard_berndt_galway_chunk_0862
import Theorems.Thm_Brocard_berndt_galway_chunk_0863
import Theorems.Thm_Brocard_berndt_galway_chunk_0864
import Theorems.Thm_Brocard_berndt_galway_chunk_0865
import Theorems.Thm_Brocard_berndt_galway_chunk_0866
import Theorems.Thm_Brocard_berndt_galway_chunk_0867
import Theorems.Thm_Brocard_berndt_galway_chunk_0868
import Theorems.Thm_Brocard_berndt_galway_chunk_0869
import Theorems.Thm_Brocard_berndt_galway_chunk_0870
import Theorems.Thm_Brocard_berndt_galway_chunk_0871
import Theorems.Thm_Brocard_berndt_galway_chunk_0872
import Theorems.Thm_Brocard_berndt_galway_chunk_0873
import Theorems.Thm_Brocard_berndt_galway_chunk_0874
import Theorems.Thm_Brocard_berndt_galway_chunk_0875
import Theorems.Thm_Brocard_berndt_galway_chunk_0876
import Theorems.Thm_Brocard_berndt_galway_chunk_0877
import Theorems.Thm_Brocard_berndt_galway_chunk_0878
import Theorems.Thm_Brocard_berndt_galway_chunk_0879
import Theorems.Thm_Brocard_berndt_galway_chunk_0880
import Theorems.Thm_Brocard_berndt_galway_chunk_0881
import Theorems.Thm_Brocard_berndt_galway_chunk_0882

theorem solution (n m : ℕ) (h1 : 150359712 ≤ n) (h2 : n < 158633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 154496402 with hs0 | hs0
  · -- n < 154496402
    rcases Nat.lt_or_ge n 152517985 with hs1 | hs1
    · -- n < 152517985
      rcases Nat.lt_or_ge n 151438848 with hs2 | hs2
      · -- n < 151438848
        rcases Nat.lt_or_ge n 150899280 with hs3 | hs3
        · -- n < 150899280
          rcases Nat.lt_or_ge n 150719424 with hs4 | hs4
          · -- n < 150719424
            rcases Nat.lt_or_ge n 150539568 with hs5 | hs5
            · -- n < 150539568
              exact Brocard.berndt_galway_chunk_0837 n m (by omega) (by omega) h
            · -- n >= 150539568
              exact Brocard.berndt_galway_chunk_0838 n m (by omega) (by omega) h
          · -- n >= 150719424
            exact Brocard.berndt_galway_chunk_0839 n m (by omega) (by omega) h
        · -- n >= 150899280
          rcases Nat.lt_or_ge n 151258992 with hs4 | hs4
          · -- n < 151258992
            rcases Nat.lt_or_ge n 151079136 with hs5 | hs5
            · -- n < 151079136
              exact Brocard.berndt_galway_chunk_0840 n m (by omega) (by omega) h
            · -- n >= 151079136
              exact Brocard.berndt_galway_chunk_0841 n m (by omega) (by omega) h
          · -- n >= 151258992
            exact Brocard.berndt_galway_chunk_0842 n m (by omega) (by omega) h
      · -- n >= 151438848
        rcases Nat.lt_or_ge n 151978417 with hs3 | hs3
        · -- n < 151978417
          rcases Nat.lt_or_ge n 151798561 with hs4 | hs4
          · -- n < 151798561
            rcases Nat.lt_or_ge n 151618705 with hs5 | hs5
            · -- n < 151618705
              exact Brocard.berndt_galway_chunk_0843 n m (by omega) (by omega) h
            · -- n >= 151618705
              exact Brocard.berndt_galway_chunk_0844 n m (by omega) (by omega) h
          · -- n >= 151798561
            exact Brocard.berndt_galway_chunk_0845 n m (by omega) (by omega) h
        · -- n >= 151978417
          rcases Nat.lt_or_ge n 152338129 with hs4 | hs4
          · -- n < 152338129
            rcases Nat.lt_or_ge n 152158273 with hs5 | hs5
            · -- n < 152158273
              exact Brocard.berndt_galway_chunk_0846 n m (by omega) (by omega) h
            · -- n >= 152158273
              exact Brocard.berndt_galway_chunk_0847 n m (by omega) (by omega) h
          · -- n >= 152338129
            exact Brocard.berndt_galway_chunk_0848 n m (by omega) (by omega) h
    · -- n >= 152517985
      rcases Nat.lt_or_ge n 153597122 with hs2 | hs2
      · -- n < 153597122
        rcases Nat.lt_or_ge n 153057553 with hs3 | hs3
        · -- n < 153057553
          rcases Nat.lt_or_ge n 152877697 with hs4 | hs4
          · -- n < 152877697
            rcases Nat.lt_or_ge n 152697841 with hs5 | hs5
            · -- n < 152697841
              exact Brocard.berndt_galway_chunk_0849 n m (by omega) (by omega) h
            · -- n >= 152697841
              exact Brocard.berndt_galway_chunk_0850 n m (by omega) (by omega) h
          · -- n >= 152877697
            exact Brocard.berndt_galway_chunk_0851 n m (by omega) (by omega) h
        · -- n >= 153057553
          rcases Nat.lt_or_ge n 153417266 with hs4 | hs4
          · -- n < 153417266
            rcases Nat.lt_or_ge n 153237410 with hs5 | hs5
            · -- n < 153237410
              exact Brocard.berndt_galway_chunk_0852 n m (by omega) (by omega) h
            · -- n >= 153237410
              exact Brocard.berndt_galway_chunk_0853 n m (by omega) (by omega) h
          · -- n >= 153417266
            exact Brocard.berndt_galway_chunk_0854 n m (by omega) (by omega) h
      · -- n >= 153597122
        rcases Nat.lt_or_ge n 154136690 with hs3 | hs3
        · -- n < 154136690
          rcases Nat.lt_or_ge n 153956834 with hs4 | hs4
          · -- n < 153956834
            rcases Nat.lt_or_ge n 153776978 with hs5 | hs5
            · -- n < 153776978
              exact Brocard.berndt_galway_chunk_0855 n m (by omega) (by omega) h
            · -- n >= 153776978
              exact Brocard.berndt_galway_chunk_0856 n m (by omega) (by omega) h
          · -- n >= 153956834
            exact Brocard.berndt_galway_chunk_0857 n m (by omega) (by omega) h
        · -- n >= 154136690
          rcases Nat.lt_or_ge n 154316546 with hs4 | hs4
          · -- n < 154316546
            exact Brocard.berndt_galway_chunk_0858 n m (by omega) (by omega) h
          · -- n >= 154316546
            exact Brocard.berndt_galway_chunk_0859 n m (by omega) (by omega) h
  · -- n >= 154496402
    rcases Nat.lt_or_ge n 156654676 with hs1 | hs1
    · -- n < 156654676
      rcases Nat.lt_or_ge n 155575539 with hs2 | hs2
      · -- n < 155575539
        rcases Nat.lt_or_ge n 155035971 with hs3 | hs3
        · -- n < 155035971
          rcases Nat.lt_or_ge n 154856115 with hs4 | hs4
          · -- n < 154856115
            rcases Nat.lt_or_ge n 154676258 with hs5 | hs5
            · -- n < 154676258
              exact Brocard.berndt_galway_chunk_0860 n m (by omega) (by omega) h
            · -- n >= 154676258
              exact Brocard.berndt_galway_chunk_0861 n m (by omega) (by omega) h
          · -- n >= 154856115
            exact Brocard.berndt_galway_chunk_0862 n m (by omega) (by omega) h
        · -- n >= 155035971
          rcases Nat.lt_or_ge n 155395683 with hs4 | hs4
          · -- n < 155395683
            rcases Nat.lt_or_ge n 155215827 with hs5 | hs5
            · -- n < 155215827
              exact Brocard.berndt_galway_chunk_0863 n m (by omega) (by omega) h
            · -- n >= 155215827
              exact Brocard.berndt_galway_chunk_0864 n m (by omega) (by omega) h
          · -- n >= 155395683
            exact Brocard.berndt_galway_chunk_0865 n m (by omega) (by omega) h
      · -- n >= 155575539
        rcases Nat.lt_or_ge n 156115107 with hs3 | hs3
        · -- n < 156115107
          rcases Nat.lt_or_ge n 155935251 with hs4 | hs4
          · -- n < 155935251
            rcases Nat.lt_or_ge n 155755395 with hs5 | hs5
            · -- n < 155755395
              exact Brocard.berndt_galway_chunk_0866 n m (by omega) (by omega) h
            · -- n >= 155755395
              exact Brocard.berndt_galway_chunk_0867 n m (by omega) (by omega) h
          · -- n >= 155935251
            exact Brocard.berndt_galway_chunk_0868 n m (by omega) (by omega) h
        · -- n >= 156115107
          rcases Nat.lt_or_ge n 156474820 with hs4 | hs4
          · -- n < 156474820
            rcases Nat.lt_or_ge n 156294964 with hs5 | hs5
            · -- n < 156294964
              exact Brocard.berndt_galway_chunk_0869 n m (by omega) (by omega) h
            · -- n >= 156294964
              exact Brocard.berndt_galway_chunk_0870 n m (by omega) (by omega) h
          · -- n >= 156474820
            exact Brocard.berndt_galway_chunk_0871 n m (by omega) (by omega) h
    · -- n >= 156654676
      rcases Nat.lt_or_ge n 157733812 with hs2 | hs2
      · -- n < 157733812
        rcases Nat.lt_or_ge n 157194244 with hs3 | hs3
        · -- n < 157194244
          rcases Nat.lt_or_ge n 157014388 with hs4 | hs4
          · -- n < 157014388
            rcases Nat.lt_or_ge n 156834532 with hs5 | hs5
            · -- n < 156834532
              exact Brocard.berndt_galway_chunk_0872 n m (by omega) (by omega) h
            · -- n >= 156834532
              exact Brocard.berndt_galway_chunk_0873 n m (by omega) (by omega) h
          · -- n >= 157014388
            exact Brocard.berndt_galway_chunk_0874 n m (by omega) (by omega) h
        · -- n >= 157194244
          rcases Nat.lt_or_ge n 157553956 with hs4 | hs4
          · -- n < 157553956
            rcases Nat.lt_or_ge n 157374100 with hs5 | hs5
            · -- n < 157374100
              exact Brocard.berndt_galway_chunk_0875 n m (by omega) (by omega) h
            · -- n >= 157374100
              exact Brocard.berndt_galway_chunk_0876 n m (by omega) (by omega) h
          · -- n >= 157553956
            exact Brocard.berndt_galway_chunk_0877 n m (by omega) (by omega) h
      · -- n >= 157733812
        rcases Nat.lt_or_ge n 158273381 with hs3 | hs3
        · -- n < 158273381
          rcases Nat.lt_or_ge n 158093525 with hs4 | hs4
          · -- n < 158093525
            rcases Nat.lt_or_ge n 157913669 with hs5 | hs5
            · -- n < 157913669
              exact Brocard.berndt_galway_chunk_0878 n m (by omega) (by omega) h
            · -- n >= 157913669
              exact Brocard.berndt_galway_chunk_0879 n m (by omega) (by omega) h
          · -- n >= 158093525
            exact Brocard.berndt_galway_chunk_0880 n m (by omega) (by omega) h
        · -- n >= 158273381
          rcases Nat.lt_or_ge n 158453237 with hs4 | hs4
          · -- n < 158453237
            exact Brocard.berndt_galway_chunk_0881 n m (by omega) (by omega) h
          · -- n >= 158453237
            exact Brocard.berndt_galway_chunk_0882 n m (by omega) (by omega) h
