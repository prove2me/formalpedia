-- Prove2me | solution 1 for Brocard.berndt_galway_group_064
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:23:58.951979+00:00
-- url     : https://prove2.me/submissions/a5c191ba-586d-4429-a9b4-0fa6d29b5648

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_2922
import Theorems.Thm_Brocard_berndt_galway_chunk_2923
import Theorems.Thm_Brocard_berndt_galway_chunk_2924
import Theorems.Thm_Brocard_berndt_galway_chunk_2925
import Theorems.Thm_Brocard_berndt_galway_chunk_2926
import Theorems.Thm_Brocard_berndt_galway_chunk_2927
import Theorems.Thm_Brocard_berndt_galway_chunk_2928
import Theorems.Thm_Brocard_berndt_galway_chunk_2929
import Theorems.Thm_Brocard_berndt_galway_chunk_2930
import Theorems.Thm_Brocard_berndt_galway_chunk_2931
import Theorems.Thm_Brocard_berndt_galway_chunk_2932
import Theorems.Thm_Brocard_berndt_galway_chunk_2933
import Theorems.Thm_Brocard_berndt_galway_chunk_2934
import Theorems.Thm_Brocard_berndt_galway_chunk_2935
import Theorems.Thm_Brocard_berndt_galway_chunk_2936
import Theorems.Thm_Brocard_berndt_galway_chunk_2937
import Theorems.Thm_Brocard_berndt_galway_chunk_2938
import Theorems.Thm_Brocard_berndt_galway_chunk_2939
import Theorems.Thm_Brocard_berndt_galway_chunk_2940
import Theorems.Thm_Brocard_berndt_galway_chunk_2941
import Theorems.Thm_Brocard_berndt_galway_chunk_2942
import Theorems.Thm_Brocard_berndt_galway_chunk_2943
import Theorems.Thm_Brocard_berndt_galway_chunk_2944
import Theorems.Thm_Brocard_berndt_galway_chunk_2945
import Theorems.Thm_Brocard_berndt_galway_chunk_2946
import Theorems.Thm_Brocard_berndt_galway_chunk_2947
import Theorems.Thm_Brocard_berndt_galway_chunk_2948
import Theorems.Thm_Brocard_berndt_galway_chunk_2949
import Theorems.Thm_Brocard_berndt_galway_chunk_2950
import Theorems.Thm_Brocard_berndt_galway_chunk_2951
import Theorems.Thm_Brocard_berndt_galway_chunk_2952
import Theorems.Thm_Brocard_berndt_galway_chunk_2953
import Theorems.Thm_Brocard_berndt_galway_chunk_2954
import Theorems.Thm_Brocard_berndt_galway_chunk_2955
import Theorems.Thm_Brocard_berndt_galway_chunk_2956
import Theorems.Thm_Brocard_berndt_galway_chunk_2957
import Theorems.Thm_Brocard_berndt_galway_chunk_2958
import Theorems.Thm_Brocard_berndt_galway_chunk_2959
import Theorems.Thm_Brocard_berndt_galway_chunk_2960
import Theorems.Thm_Brocard_berndt_galway_chunk_2961
import Theorems.Thm_Brocard_berndt_galway_chunk_2962
import Theorems.Thm_Brocard_berndt_galway_chunk_2963
import Theorems.Thm_Brocard_berndt_galway_chunk_2964
import Theorems.Thm_Brocard_berndt_galway_chunk_2965
import Theorems.Thm_Brocard_berndt_galway_chunk_2966
import Theorems.Thm_Brocard_berndt_galway_chunk_2967
import Theorems.Thm_Brocard_berndt_galway_chunk_2968

theorem solution (n m : ℕ) (h1 : 525359712 ≤ n) (h2 : n < 533812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 529676258 with hs0 | hs0
  · -- n < 529676258
    rcases Nat.lt_or_ge n 527517985 with hs1 | hs1
    · -- n < 527517985
      rcases Nat.lt_or_ge n 526438848 with hs2 | hs2
      · -- n < 526438848
        rcases Nat.lt_or_ge n 525899280 with hs3 | hs3
        · -- n < 525899280
          rcases Nat.lt_or_ge n 525719424 with hs4 | hs4
          · -- n < 525719424
            rcases Nat.lt_or_ge n 525539568 with hs5 | hs5
            · -- n < 525539568
              exact Brocard.berndt_galway_chunk_2922 n m (by omega) (by omega) h
            · -- n >= 525539568
              exact Brocard.berndt_galway_chunk_2923 n m (by omega) (by omega) h
          · -- n >= 525719424
            exact Brocard.berndt_galway_chunk_2924 n m (by omega) (by omega) h
        · -- n >= 525899280
          rcases Nat.lt_or_ge n 526258992 with hs4 | hs4
          · -- n < 526258992
            rcases Nat.lt_or_ge n 526079136 with hs5 | hs5
            · -- n < 526079136
              exact Brocard.berndt_galway_chunk_2925 n m (by omega) (by omega) h
            · -- n >= 526079136
              exact Brocard.berndt_galway_chunk_2926 n m (by omega) (by omega) h
          · -- n >= 526258992
            exact Brocard.berndt_galway_chunk_2927 n m (by omega) (by omega) h
      · -- n >= 526438848
        rcases Nat.lt_or_ge n 526978417 with hs3 | hs3
        · -- n < 526978417
          rcases Nat.lt_or_ge n 526798561 with hs4 | hs4
          · -- n < 526798561
            rcases Nat.lt_or_ge n 526618705 with hs5 | hs5
            · -- n < 526618705
              exact Brocard.berndt_galway_chunk_2928 n m (by omega) (by omega) h
            · -- n >= 526618705
              exact Brocard.berndt_galway_chunk_2929 n m (by omega) (by omega) h
          · -- n >= 526798561
            exact Brocard.berndt_galway_chunk_2930 n m (by omega) (by omega) h
        · -- n >= 526978417
          rcases Nat.lt_or_ge n 527338129 with hs4 | hs4
          · -- n < 527338129
            rcases Nat.lt_or_ge n 527158273 with hs5 | hs5
            · -- n < 527158273
              exact Brocard.berndt_galway_chunk_2931 n m (by omega) (by omega) h
            · -- n >= 527158273
              exact Brocard.berndt_galway_chunk_2932 n m (by omega) (by omega) h
          · -- n >= 527338129
            exact Brocard.berndt_galway_chunk_2933 n m (by omega) (by omega) h
    · -- n >= 527517985
      rcases Nat.lt_or_ge n 528597122 with hs2 | hs2
      · -- n < 528597122
        rcases Nat.lt_or_ge n 528057553 with hs3 | hs3
        · -- n < 528057553
          rcases Nat.lt_or_ge n 527877697 with hs4 | hs4
          · -- n < 527877697
            rcases Nat.lt_or_ge n 527697841 with hs5 | hs5
            · -- n < 527697841
              exact Brocard.berndt_galway_chunk_2934 n m (by omega) (by omega) h
            · -- n >= 527697841
              exact Brocard.berndt_galway_chunk_2935 n m (by omega) (by omega) h
          · -- n >= 527877697
            exact Brocard.berndt_galway_chunk_2936 n m (by omega) (by omega) h
        · -- n >= 528057553
          rcases Nat.lt_or_ge n 528417266 with hs4 | hs4
          · -- n < 528417266
            rcases Nat.lt_or_ge n 528237410 with hs5 | hs5
            · -- n < 528237410
              exact Brocard.berndt_galway_chunk_2937 n m (by omega) (by omega) h
            · -- n >= 528237410
              exact Brocard.berndt_galway_chunk_2938 n m (by omega) (by omega) h
          · -- n >= 528417266
            exact Brocard.berndt_galway_chunk_2939 n m (by omega) (by omega) h
      · -- n >= 528597122
        rcases Nat.lt_or_ge n 529136690 with hs3 | hs3
        · -- n < 529136690
          rcases Nat.lt_or_ge n 528956834 with hs4 | hs4
          · -- n < 528956834
            rcases Nat.lt_or_ge n 528776978 with hs5 | hs5
            · -- n < 528776978
              exact Brocard.berndt_galway_chunk_2940 n m (by omega) (by omega) h
            · -- n >= 528776978
              exact Brocard.berndt_galway_chunk_2941 n m (by omega) (by omega) h
          · -- n >= 528956834
            exact Brocard.berndt_galway_chunk_2942 n m (by omega) (by omega) h
        · -- n >= 529136690
          rcases Nat.lt_or_ge n 529496402 with hs4 | hs4
          · -- n < 529496402
            rcases Nat.lt_or_ge n 529316546 with hs5 | hs5
            · -- n < 529316546
              exact Brocard.berndt_galway_chunk_2943 n m (by omega) (by omega) h
            · -- n >= 529316546
              exact Brocard.berndt_galway_chunk_2944 n m (by omega) (by omega) h
          · -- n >= 529496402
            exact Brocard.berndt_galway_chunk_2945 n m (by omega) (by omega) h
  · -- n >= 529676258
    rcases Nat.lt_or_ge n 531834532 with hs1 | hs1
    · -- n < 531834532
      rcases Nat.lt_or_ge n 530755395 with hs2 | hs2
      · -- n < 530755395
        rcases Nat.lt_or_ge n 530215827 with hs3 | hs3
        · -- n < 530215827
          rcases Nat.lt_or_ge n 530035971 with hs4 | hs4
          · -- n < 530035971
            rcases Nat.lt_or_ge n 529856115 with hs5 | hs5
            · -- n < 529856115
              exact Brocard.berndt_galway_chunk_2946 n m (by omega) (by omega) h
            · -- n >= 529856115
              exact Brocard.berndt_galway_chunk_2947 n m (by omega) (by omega) h
          · -- n >= 530035971
            exact Brocard.berndt_galway_chunk_2948 n m (by omega) (by omega) h
        · -- n >= 530215827
          rcases Nat.lt_or_ge n 530575539 with hs4 | hs4
          · -- n < 530575539
            rcases Nat.lt_or_ge n 530395683 with hs5 | hs5
            · -- n < 530395683
              exact Brocard.berndt_galway_chunk_2949 n m (by omega) (by omega) h
            · -- n >= 530395683
              exact Brocard.berndt_galway_chunk_2950 n m (by omega) (by omega) h
          · -- n >= 530575539
            exact Brocard.berndt_galway_chunk_2951 n m (by omega) (by omega) h
      · -- n >= 530755395
        rcases Nat.lt_or_ge n 531294964 with hs3 | hs3
        · -- n < 531294964
          rcases Nat.lt_or_ge n 531115107 with hs4 | hs4
          · -- n < 531115107
            rcases Nat.lt_or_ge n 530935251 with hs5 | hs5
            · -- n < 530935251
              exact Brocard.berndt_galway_chunk_2952 n m (by omega) (by omega) h
            · -- n >= 530935251
              exact Brocard.berndt_galway_chunk_2953 n m (by omega) (by omega) h
          · -- n >= 531115107
            exact Brocard.berndt_galway_chunk_2954 n m (by omega) (by omega) h
        · -- n >= 531294964
          rcases Nat.lt_or_ge n 531654676 with hs4 | hs4
          · -- n < 531654676
            rcases Nat.lt_or_ge n 531474820 with hs5 | hs5
            · -- n < 531474820
              exact Brocard.berndt_galway_chunk_2955 n m (by omega) (by omega) h
            · -- n >= 531474820
              exact Brocard.berndt_galway_chunk_2956 n m (by omega) (by omega) h
          · -- n >= 531654676
            exact Brocard.berndt_galway_chunk_2957 n m (by omega) (by omega) h
    · -- n >= 531834532
      rcases Nat.lt_or_ge n 532913669 with hs2 | hs2
      · -- n < 532913669
        rcases Nat.lt_or_ge n 532374100 with hs3 | hs3
        · -- n < 532374100
          rcases Nat.lt_or_ge n 532194244 with hs4 | hs4
          · -- n < 532194244
            rcases Nat.lt_or_ge n 532014388 with hs5 | hs5
            · -- n < 532014388
              exact Brocard.berndt_galway_chunk_2958 n m (by omega) (by omega) h
            · -- n >= 532014388
              exact Brocard.berndt_galway_chunk_2959 n m (by omega) (by omega) h
          · -- n >= 532194244
            exact Brocard.berndt_galway_chunk_2960 n m (by omega) (by omega) h
        · -- n >= 532374100
          rcases Nat.lt_or_ge n 532733812 with hs4 | hs4
          · -- n < 532733812
            rcases Nat.lt_or_ge n 532553956 with hs5 | hs5
            · -- n < 532553956
              exact Brocard.berndt_galway_chunk_2961 n m (by omega) (by omega) h
            · -- n >= 532553956
              exact Brocard.berndt_galway_chunk_2962 n m (by omega) (by omega) h
          · -- n >= 532733812
            exact Brocard.berndt_galway_chunk_2963 n m (by omega) (by omega) h
      · -- n >= 532913669
        rcases Nat.lt_or_ge n 533453237 with hs3 | hs3
        · -- n < 533453237
          rcases Nat.lt_or_ge n 533273381 with hs4 | hs4
          · -- n < 533273381
            rcases Nat.lt_or_ge n 533093525 with hs5 | hs5
            · -- n < 533093525
              exact Brocard.berndt_galway_chunk_2964 n m (by omega) (by omega) h
            · -- n >= 533093525
              exact Brocard.berndt_galway_chunk_2965 n m (by omega) (by omega) h
          · -- n >= 533273381
            exact Brocard.berndt_galway_chunk_2966 n m (by omega) (by omega) h
        · -- n >= 533453237
          rcases Nat.lt_or_ge n 533633093 with hs4 | hs4
          · -- n < 533633093
            exact Brocard.berndt_galway_chunk_2967 n m (by omega) (by omega) h
          · -- n >= 533633093
            exact Brocard.berndt_galway_chunk_2968 n m (by omega) (by omega) h
