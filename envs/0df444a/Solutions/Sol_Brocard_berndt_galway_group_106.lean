-- Prove2me | solution 1 for Brocard.berndt_galway_group_106
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:16:25.343524+00:00
-- url     : https://prove2.me/submissions/1650fc13-7e0e-4791-a83f-5123907f188c

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_4867
import Theorems.Thm_Brocard_berndt_galway_chunk_4868
import Theorems.Thm_Brocard_berndt_galway_chunk_4869
import Theorems.Thm_Brocard_berndt_galway_chunk_4870
import Theorems.Thm_Brocard_berndt_galway_chunk_4871
import Theorems.Thm_Brocard_berndt_galway_chunk_4872
import Theorems.Thm_Brocard_berndt_galway_chunk_4873
import Theorems.Thm_Brocard_berndt_galway_chunk_4874
import Theorems.Thm_Brocard_berndt_galway_chunk_4875
import Theorems.Thm_Brocard_berndt_galway_chunk_4876
import Theorems.Thm_Brocard_berndt_galway_chunk_4877
import Theorems.Thm_Brocard_berndt_galway_chunk_4878
import Theorems.Thm_Brocard_berndt_galway_chunk_4879
import Theorems.Thm_Brocard_berndt_galway_chunk_4880
import Theorems.Thm_Brocard_berndt_galway_chunk_4881
import Theorems.Thm_Brocard_berndt_galway_chunk_4882
import Theorems.Thm_Brocard_berndt_galway_chunk_4883
import Theorems.Thm_Brocard_berndt_galway_chunk_4884
import Theorems.Thm_Brocard_berndt_galway_chunk_4885
import Theorems.Thm_Brocard_berndt_galway_chunk_4886
import Theorems.Thm_Brocard_berndt_galway_chunk_4887
import Theorems.Thm_Brocard_berndt_galway_chunk_4888
import Theorems.Thm_Brocard_berndt_galway_chunk_4889
import Theorems.Thm_Brocard_berndt_galway_chunk_4890
import Theorems.Thm_Brocard_berndt_galway_chunk_4891
import Theorems.Thm_Brocard_berndt_galway_chunk_4892
import Theorems.Thm_Brocard_berndt_galway_chunk_4893
import Theorems.Thm_Brocard_berndt_galway_chunk_4894
import Theorems.Thm_Brocard_berndt_galway_chunk_4895
import Theorems.Thm_Brocard_berndt_galway_chunk_4896
import Theorems.Thm_Brocard_berndt_galway_chunk_4897
import Theorems.Thm_Brocard_berndt_galway_chunk_4898
import Theorems.Thm_Brocard_berndt_galway_chunk_4899
import Theorems.Thm_Brocard_berndt_galway_chunk_4900
import Theorems.Thm_Brocard_berndt_galway_chunk_4901
import Theorems.Thm_Brocard_berndt_galway_chunk_4902
import Theorems.Thm_Brocard_berndt_galway_chunk_4903
import Theorems.Thm_Brocard_berndt_galway_chunk_4904
import Theorems.Thm_Brocard_berndt_galway_chunk_4905
import Theorems.Thm_Brocard_berndt_galway_chunk_4906
import Theorems.Thm_Brocard_berndt_galway_chunk_4907
import Theorems.Thm_Brocard_berndt_galway_chunk_4908
import Theorems.Thm_Brocard_berndt_galway_chunk_4909
import Theorems.Thm_Brocard_berndt_galway_chunk_4910
import Theorems.Thm_Brocard_berndt_galway_chunk_4911
import Theorems.Thm_Brocard_berndt_galway_chunk_4912

theorem solution (n m : ℕ) (h1 : 875179856 ≤ n) (h2 : n < 883453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 879316546 with hs0 | hs0
  · -- n < 879316546
    rcases Nat.lt_or_ge n 877338129 with hs1 | hs1
    · -- n < 877338129
      rcases Nat.lt_or_ge n 876258992 with hs2 | hs2
      · -- n < 876258992
        rcases Nat.lt_or_ge n 875719424 with hs3 | hs3
        · -- n < 875719424
          rcases Nat.lt_or_ge n 875539568 with hs4 | hs4
          · -- n < 875539568
            rcases Nat.lt_or_ge n 875359712 with hs5 | hs5
            · -- n < 875359712
              exact Brocard.berndt_galway_chunk_4867 n m (by omega) (by omega) h
            · -- n >= 875359712
              exact Brocard.berndt_galway_chunk_4868 n m (by omega) (by omega) h
          · -- n >= 875539568
            exact Brocard.berndt_galway_chunk_4869 n m (by omega) (by omega) h
        · -- n >= 875719424
          rcases Nat.lt_or_ge n 876079136 with hs4 | hs4
          · -- n < 876079136
            rcases Nat.lt_or_ge n 875899280 with hs5 | hs5
            · -- n < 875899280
              exact Brocard.berndt_galway_chunk_4870 n m (by omega) (by omega) h
            · -- n >= 875899280
              exact Brocard.berndt_galway_chunk_4871 n m (by omega) (by omega) h
          · -- n >= 876079136
            exact Brocard.berndt_galway_chunk_4872 n m (by omega) (by omega) h
      · -- n >= 876258992
        rcases Nat.lt_or_ge n 876798561 with hs3 | hs3
        · -- n < 876798561
          rcases Nat.lt_or_ge n 876618705 with hs4 | hs4
          · -- n < 876618705
            rcases Nat.lt_or_ge n 876438848 with hs5 | hs5
            · -- n < 876438848
              exact Brocard.berndt_galway_chunk_4873 n m (by omega) (by omega) h
            · -- n >= 876438848
              exact Brocard.berndt_galway_chunk_4874 n m (by omega) (by omega) h
          · -- n >= 876618705
            exact Brocard.berndt_galway_chunk_4875 n m (by omega) (by omega) h
        · -- n >= 876798561
          rcases Nat.lt_or_ge n 877158273 with hs4 | hs4
          · -- n < 877158273
            rcases Nat.lt_or_ge n 876978417 with hs5 | hs5
            · -- n < 876978417
              exact Brocard.berndt_galway_chunk_4876 n m (by omega) (by omega) h
            · -- n >= 876978417
              exact Brocard.berndt_galway_chunk_4877 n m (by omega) (by omega) h
          · -- n >= 877158273
            exact Brocard.berndt_galway_chunk_4878 n m (by omega) (by omega) h
    · -- n >= 877338129
      rcases Nat.lt_or_ge n 878417266 with hs2 | hs2
      · -- n < 878417266
        rcases Nat.lt_or_ge n 877877697 with hs3 | hs3
        · -- n < 877877697
          rcases Nat.lt_or_ge n 877697841 with hs4 | hs4
          · -- n < 877697841
            rcases Nat.lt_or_ge n 877517985 with hs5 | hs5
            · -- n < 877517985
              exact Brocard.berndt_galway_chunk_4879 n m (by omega) (by omega) h
            · -- n >= 877517985
              exact Brocard.berndt_galway_chunk_4880 n m (by omega) (by omega) h
          · -- n >= 877697841
            exact Brocard.berndt_galway_chunk_4881 n m (by omega) (by omega) h
        · -- n >= 877877697
          rcases Nat.lt_or_ge n 878237410 with hs4 | hs4
          · -- n < 878237410
            rcases Nat.lt_or_ge n 878057553 with hs5 | hs5
            · -- n < 878057553
              exact Brocard.berndt_galway_chunk_4882 n m (by omega) (by omega) h
            · -- n >= 878057553
              exact Brocard.berndt_galway_chunk_4883 n m (by omega) (by omega) h
          · -- n >= 878237410
            exact Brocard.berndt_galway_chunk_4884 n m (by omega) (by omega) h
      · -- n >= 878417266
        rcases Nat.lt_or_ge n 878956834 with hs3 | hs3
        · -- n < 878956834
          rcases Nat.lt_or_ge n 878776978 with hs4 | hs4
          · -- n < 878776978
            rcases Nat.lt_or_ge n 878597122 with hs5 | hs5
            · -- n < 878597122
              exact Brocard.berndt_galway_chunk_4885 n m (by omega) (by omega) h
            · -- n >= 878597122
              exact Brocard.berndt_galway_chunk_4886 n m (by omega) (by omega) h
          · -- n >= 878776978
            exact Brocard.berndt_galway_chunk_4887 n m (by omega) (by omega) h
        · -- n >= 878956834
          rcases Nat.lt_or_ge n 879136690 with hs4 | hs4
          · -- n < 879136690
            exact Brocard.berndt_galway_chunk_4888 n m (by omega) (by omega) h
          · -- n >= 879136690
            exact Brocard.berndt_galway_chunk_4889 n m (by omega) (by omega) h
  · -- n >= 879316546
    rcases Nat.lt_or_ge n 881474820 with hs1 | hs1
    · -- n < 881474820
      rcases Nat.lt_or_ge n 880395683 with hs2 | hs2
      · -- n < 880395683
        rcases Nat.lt_or_ge n 879856115 with hs3 | hs3
        · -- n < 879856115
          rcases Nat.lt_or_ge n 879676258 with hs4 | hs4
          · -- n < 879676258
            rcases Nat.lt_or_ge n 879496402 with hs5 | hs5
            · -- n < 879496402
              exact Brocard.berndt_galway_chunk_4890 n m (by omega) (by omega) h
            · -- n >= 879496402
              exact Brocard.berndt_galway_chunk_4891 n m (by omega) (by omega) h
          · -- n >= 879676258
            exact Brocard.berndt_galway_chunk_4892 n m (by omega) (by omega) h
        · -- n >= 879856115
          rcases Nat.lt_or_ge n 880215827 with hs4 | hs4
          · -- n < 880215827
            rcases Nat.lt_or_ge n 880035971 with hs5 | hs5
            · -- n < 880035971
              exact Brocard.berndt_galway_chunk_4893 n m (by omega) (by omega) h
            · -- n >= 880035971
              exact Brocard.berndt_galway_chunk_4894 n m (by omega) (by omega) h
          · -- n >= 880215827
            exact Brocard.berndt_galway_chunk_4895 n m (by omega) (by omega) h
      · -- n >= 880395683
        rcases Nat.lt_or_ge n 880935251 with hs3 | hs3
        · -- n < 880935251
          rcases Nat.lt_or_ge n 880755395 with hs4 | hs4
          · -- n < 880755395
            rcases Nat.lt_or_ge n 880575539 with hs5 | hs5
            · -- n < 880575539
              exact Brocard.berndt_galway_chunk_4896 n m (by omega) (by omega) h
            · -- n >= 880575539
              exact Brocard.berndt_galway_chunk_4897 n m (by omega) (by omega) h
          · -- n >= 880755395
            exact Brocard.berndt_galway_chunk_4898 n m (by omega) (by omega) h
        · -- n >= 880935251
          rcases Nat.lt_or_ge n 881294964 with hs4 | hs4
          · -- n < 881294964
            rcases Nat.lt_or_ge n 881115107 with hs5 | hs5
            · -- n < 881115107
              exact Brocard.berndt_galway_chunk_4899 n m (by omega) (by omega) h
            · -- n >= 881115107
              exact Brocard.berndt_galway_chunk_4900 n m (by omega) (by omega) h
          · -- n >= 881294964
            exact Brocard.berndt_galway_chunk_4901 n m (by omega) (by omega) h
    · -- n >= 881474820
      rcases Nat.lt_or_ge n 882553956 with hs2 | hs2
      · -- n < 882553956
        rcases Nat.lt_or_ge n 882014388 with hs3 | hs3
        · -- n < 882014388
          rcases Nat.lt_or_ge n 881834532 with hs4 | hs4
          · -- n < 881834532
            rcases Nat.lt_or_ge n 881654676 with hs5 | hs5
            · -- n < 881654676
              exact Brocard.berndt_galway_chunk_4902 n m (by omega) (by omega) h
            · -- n >= 881654676
              exact Brocard.berndt_galway_chunk_4903 n m (by omega) (by omega) h
          · -- n >= 881834532
            exact Brocard.berndt_galway_chunk_4904 n m (by omega) (by omega) h
        · -- n >= 882014388
          rcases Nat.lt_or_ge n 882374100 with hs4 | hs4
          · -- n < 882374100
            rcases Nat.lt_or_ge n 882194244 with hs5 | hs5
            · -- n < 882194244
              exact Brocard.berndt_galway_chunk_4905 n m (by omega) (by omega) h
            · -- n >= 882194244
              exact Brocard.berndt_galway_chunk_4906 n m (by omega) (by omega) h
          · -- n >= 882374100
            exact Brocard.berndt_galway_chunk_4907 n m (by omega) (by omega) h
      · -- n >= 882553956
        rcases Nat.lt_or_ge n 883093525 with hs3 | hs3
        · -- n < 883093525
          rcases Nat.lt_or_ge n 882913669 with hs4 | hs4
          · -- n < 882913669
            rcases Nat.lt_or_ge n 882733812 with hs5 | hs5
            · -- n < 882733812
              exact Brocard.berndt_galway_chunk_4908 n m (by omega) (by omega) h
            · -- n >= 882733812
              exact Brocard.berndt_galway_chunk_4909 n m (by omega) (by omega) h
          · -- n >= 882913669
            exact Brocard.berndt_galway_chunk_4910 n m (by omega) (by omega) h
        · -- n >= 883093525
          rcases Nat.lt_or_ge n 883273381 with hs4 | hs4
          · -- n < 883273381
            exact Brocard.berndt_galway_chunk_4911 n m (by omega) (by omega) h
          · -- n >= 883273381
            exact Brocard.berndt_galway_chunk_4912 n m (by omega) (by omega) h
