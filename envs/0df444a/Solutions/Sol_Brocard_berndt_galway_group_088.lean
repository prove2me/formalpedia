-- Prove2me | solution 1 for Brocard.berndt_galway_group_088
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:36:06.8273+00:00
-- url     : https://prove2.me/submissions/271721ec-1668-4548-8b07-ad5e33bf1365

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_4034
import Theorems.Thm_Brocard_berndt_galway_chunk_4035
import Theorems.Thm_Brocard_berndt_galway_chunk_4036
import Theorems.Thm_Brocard_berndt_galway_chunk_4037
import Theorems.Thm_Brocard_berndt_galway_chunk_4038
import Theorems.Thm_Brocard_berndt_galway_chunk_4039
import Theorems.Thm_Brocard_berndt_galway_chunk_4040
import Theorems.Thm_Brocard_berndt_galway_chunk_4041
import Theorems.Thm_Brocard_berndt_galway_chunk_4042
import Theorems.Thm_Brocard_berndt_galway_chunk_4043
import Theorems.Thm_Brocard_berndt_galway_chunk_4044
import Theorems.Thm_Brocard_berndt_galway_chunk_4045
import Theorems.Thm_Brocard_berndt_galway_chunk_4046
import Theorems.Thm_Brocard_berndt_galway_chunk_4047
import Theorems.Thm_Brocard_berndt_galway_chunk_4048
import Theorems.Thm_Brocard_berndt_galway_chunk_4049
import Theorems.Thm_Brocard_berndt_galway_chunk_4050
import Theorems.Thm_Brocard_berndt_galway_chunk_4051
import Theorems.Thm_Brocard_berndt_galway_chunk_4052
import Theorems.Thm_Brocard_berndt_galway_chunk_4053
import Theorems.Thm_Brocard_berndt_galway_chunk_4054
import Theorems.Thm_Brocard_berndt_galway_chunk_4055
import Theorems.Thm_Brocard_berndt_galway_chunk_4056
import Theorems.Thm_Brocard_berndt_galway_chunk_4057
import Theorems.Thm_Brocard_berndt_galway_chunk_4058
import Theorems.Thm_Brocard_berndt_galway_chunk_4059
import Theorems.Thm_Brocard_berndt_galway_chunk_4060
import Theorems.Thm_Brocard_berndt_galway_chunk_4061
import Theorems.Thm_Brocard_berndt_galway_chunk_4062
import Theorems.Thm_Brocard_berndt_galway_chunk_4063
import Theorems.Thm_Brocard_berndt_galway_chunk_4064
import Theorems.Thm_Brocard_berndt_galway_chunk_4065
import Theorems.Thm_Brocard_berndt_galway_chunk_4066
import Theorems.Thm_Brocard_berndt_galway_chunk_4067
import Theorems.Thm_Brocard_berndt_galway_chunk_4068
import Theorems.Thm_Brocard_berndt_galway_chunk_4069
import Theorems.Thm_Brocard_berndt_galway_chunk_4070
import Theorems.Thm_Brocard_berndt_galway_chunk_4071
import Theorems.Thm_Brocard_berndt_galway_chunk_4072
import Theorems.Thm_Brocard_berndt_galway_chunk_4073
import Theorems.Thm_Brocard_berndt_galway_chunk_4074
import Theorems.Thm_Brocard_berndt_galway_chunk_4075
import Theorems.Thm_Brocard_berndt_galway_chunk_4076
import Theorems.Thm_Brocard_berndt_galway_chunk_4077
import Theorems.Thm_Brocard_berndt_galway_chunk_4078
import Theorems.Thm_Brocard_berndt_galway_chunk_4079
import Theorems.Thm_Brocard_berndt_galway_chunk_4080

theorem solution (n m : ℕ) (h1 : 725359712 ≤ n) (h2 : n < 733812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 729676258 with hs0 | hs0
  · -- n < 729676258
    rcases Nat.lt_or_ge n 727517985 with hs1 | hs1
    · -- n < 727517985
      rcases Nat.lt_or_ge n 726438848 with hs2 | hs2
      · -- n < 726438848
        rcases Nat.lt_or_ge n 725899280 with hs3 | hs3
        · -- n < 725899280
          rcases Nat.lt_or_ge n 725719424 with hs4 | hs4
          · -- n < 725719424
            rcases Nat.lt_or_ge n 725539568 with hs5 | hs5
            · -- n < 725539568
              exact Brocard.berndt_galway_chunk_4034 n m (by omega) (by omega) h
            · -- n >= 725539568
              exact Brocard.berndt_galway_chunk_4035 n m (by omega) (by omega) h
          · -- n >= 725719424
            exact Brocard.berndt_galway_chunk_4036 n m (by omega) (by omega) h
        · -- n >= 725899280
          rcases Nat.lt_or_ge n 726258992 with hs4 | hs4
          · -- n < 726258992
            rcases Nat.lt_or_ge n 726079136 with hs5 | hs5
            · -- n < 726079136
              exact Brocard.berndt_galway_chunk_4037 n m (by omega) (by omega) h
            · -- n >= 726079136
              exact Brocard.berndt_galway_chunk_4038 n m (by omega) (by omega) h
          · -- n >= 726258992
            exact Brocard.berndt_galway_chunk_4039 n m (by omega) (by omega) h
      · -- n >= 726438848
        rcases Nat.lt_or_ge n 726978417 with hs3 | hs3
        · -- n < 726978417
          rcases Nat.lt_or_ge n 726798561 with hs4 | hs4
          · -- n < 726798561
            rcases Nat.lt_or_ge n 726618705 with hs5 | hs5
            · -- n < 726618705
              exact Brocard.berndt_galway_chunk_4040 n m (by omega) (by omega) h
            · -- n >= 726618705
              exact Brocard.berndt_galway_chunk_4041 n m (by omega) (by omega) h
          · -- n >= 726798561
            exact Brocard.berndt_galway_chunk_4042 n m (by omega) (by omega) h
        · -- n >= 726978417
          rcases Nat.lt_or_ge n 727338129 with hs4 | hs4
          · -- n < 727338129
            rcases Nat.lt_or_ge n 727158273 with hs5 | hs5
            · -- n < 727158273
              exact Brocard.berndt_galway_chunk_4043 n m (by omega) (by omega) h
            · -- n >= 727158273
              exact Brocard.berndt_galway_chunk_4044 n m (by omega) (by omega) h
          · -- n >= 727338129
            exact Brocard.berndt_galway_chunk_4045 n m (by omega) (by omega) h
    · -- n >= 727517985
      rcases Nat.lt_or_ge n 728597122 with hs2 | hs2
      · -- n < 728597122
        rcases Nat.lt_or_ge n 728057553 with hs3 | hs3
        · -- n < 728057553
          rcases Nat.lt_or_ge n 727877697 with hs4 | hs4
          · -- n < 727877697
            rcases Nat.lt_or_ge n 727697841 with hs5 | hs5
            · -- n < 727697841
              exact Brocard.berndt_galway_chunk_4046 n m (by omega) (by omega) h
            · -- n >= 727697841
              exact Brocard.berndt_galway_chunk_4047 n m (by omega) (by omega) h
          · -- n >= 727877697
            exact Brocard.berndt_galway_chunk_4048 n m (by omega) (by omega) h
        · -- n >= 728057553
          rcases Nat.lt_or_ge n 728417266 with hs4 | hs4
          · -- n < 728417266
            rcases Nat.lt_or_ge n 728237410 with hs5 | hs5
            · -- n < 728237410
              exact Brocard.berndt_galway_chunk_4049 n m (by omega) (by omega) h
            · -- n >= 728237410
              exact Brocard.berndt_galway_chunk_4050 n m (by omega) (by omega) h
          · -- n >= 728417266
            exact Brocard.berndt_galway_chunk_4051 n m (by omega) (by omega) h
      · -- n >= 728597122
        rcases Nat.lt_or_ge n 729136690 with hs3 | hs3
        · -- n < 729136690
          rcases Nat.lt_or_ge n 728956834 with hs4 | hs4
          · -- n < 728956834
            rcases Nat.lt_or_ge n 728776978 with hs5 | hs5
            · -- n < 728776978
              exact Brocard.berndt_galway_chunk_4052 n m (by omega) (by omega) h
            · -- n >= 728776978
              exact Brocard.berndt_galway_chunk_4053 n m (by omega) (by omega) h
          · -- n >= 728956834
            exact Brocard.berndt_galway_chunk_4054 n m (by omega) (by omega) h
        · -- n >= 729136690
          rcases Nat.lt_or_ge n 729496402 with hs4 | hs4
          · -- n < 729496402
            rcases Nat.lt_or_ge n 729316546 with hs5 | hs5
            · -- n < 729316546
              exact Brocard.berndt_galway_chunk_4055 n m (by omega) (by omega) h
            · -- n >= 729316546
              exact Brocard.berndt_galway_chunk_4056 n m (by omega) (by omega) h
          · -- n >= 729496402
            exact Brocard.berndt_galway_chunk_4057 n m (by omega) (by omega) h
  · -- n >= 729676258
    rcases Nat.lt_or_ge n 731834532 with hs1 | hs1
    · -- n < 731834532
      rcases Nat.lt_or_ge n 730755395 with hs2 | hs2
      · -- n < 730755395
        rcases Nat.lt_or_ge n 730215827 with hs3 | hs3
        · -- n < 730215827
          rcases Nat.lt_or_ge n 730035971 with hs4 | hs4
          · -- n < 730035971
            rcases Nat.lt_or_ge n 729856115 with hs5 | hs5
            · -- n < 729856115
              exact Brocard.berndt_galway_chunk_4058 n m (by omega) (by omega) h
            · -- n >= 729856115
              exact Brocard.berndt_galway_chunk_4059 n m (by omega) (by omega) h
          · -- n >= 730035971
            exact Brocard.berndt_galway_chunk_4060 n m (by omega) (by omega) h
        · -- n >= 730215827
          rcases Nat.lt_or_ge n 730575539 with hs4 | hs4
          · -- n < 730575539
            rcases Nat.lt_or_ge n 730395683 with hs5 | hs5
            · -- n < 730395683
              exact Brocard.berndt_galway_chunk_4061 n m (by omega) (by omega) h
            · -- n >= 730395683
              exact Brocard.berndt_galway_chunk_4062 n m (by omega) (by omega) h
          · -- n >= 730575539
            exact Brocard.berndt_galway_chunk_4063 n m (by omega) (by omega) h
      · -- n >= 730755395
        rcases Nat.lt_or_ge n 731294964 with hs3 | hs3
        · -- n < 731294964
          rcases Nat.lt_or_ge n 731115107 with hs4 | hs4
          · -- n < 731115107
            rcases Nat.lt_or_ge n 730935251 with hs5 | hs5
            · -- n < 730935251
              exact Brocard.berndt_galway_chunk_4064 n m (by omega) (by omega) h
            · -- n >= 730935251
              exact Brocard.berndt_galway_chunk_4065 n m (by omega) (by omega) h
          · -- n >= 731115107
            exact Brocard.berndt_galway_chunk_4066 n m (by omega) (by omega) h
        · -- n >= 731294964
          rcases Nat.lt_or_ge n 731654676 with hs4 | hs4
          · -- n < 731654676
            rcases Nat.lt_or_ge n 731474820 with hs5 | hs5
            · -- n < 731474820
              exact Brocard.berndt_galway_chunk_4067 n m (by omega) (by omega) h
            · -- n >= 731474820
              exact Brocard.berndt_galway_chunk_4068 n m (by omega) (by omega) h
          · -- n >= 731654676
            exact Brocard.berndt_galway_chunk_4069 n m (by omega) (by omega) h
    · -- n >= 731834532
      rcases Nat.lt_or_ge n 732913669 with hs2 | hs2
      · -- n < 732913669
        rcases Nat.lt_or_ge n 732374100 with hs3 | hs3
        · -- n < 732374100
          rcases Nat.lt_or_ge n 732194244 with hs4 | hs4
          · -- n < 732194244
            rcases Nat.lt_or_ge n 732014388 with hs5 | hs5
            · -- n < 732014388
              exact Brocard.berndt_galway_chunk_4070 n m (by omega) (by omega) h
            · -- n >= 732014388
              exact Brocard.berndt_galway_chunk_4071 n m (by omega) (by omega) h
          · -- n >= 732194244
            exact Brocard.berndt_galway_chunk_4072 n m (by omega) (by omega) h
        · -- n >= 732374100
          rcases Nat.lt_or_ge n 732733812 with hs4 | hs4
          · -- n < 732733812
            rcases Nat.lt_or_ge n 732553956 with hs5 | hs5
            · -- n < 732553956
              exact Brocard.berndt_galway_chunk_4073 n m (by omega) (by omega) h
            · -- n >= 732553956
              exact Brocard.berndt_galway_chunk_4074 n m (by omega) (by omega) h
          · -- n >= 732733812
            exact Brocard.berndt_galway_chunk_4075 n m (by omega) (by omega) h
      · -- n >= 732913669
        rcases Nat.lt_or_ge n 733453237 with hs3 | hs3
        · -- n < 733453237
          rcases Nat.lt_or_ge n 733273381 with hs4 | hs4
          · -- n < 733273381
            rcases Nat.lt_or_ge n 733093525 with hs5 | hs5
            · -- n < 733093525
              exact Brocard.berndt_galway_chunk_4076 n m (by omega) (by omega) h
            · -- n >= 733093525
              exact Brocard.berndt_galway_chunk_4077 n m (by omega) (by omega) h
          · -- n >= 733273381
            exact Brocard.berndt_galway_chunk_4078 n m (by omega) (by omega) h
        · -- n >= 733453237
          rcases Nat.lt_or_ge n 733633093 with hs4 | hs4
          · -- n < 733633093
            exact Brocard.berndt_galway_chunk_4079 n m (by omega) (by omega) h
          · -- n >= 733633093
            exact Brocard.berndt_galway_chunk_4080 n m (by omega) (by omega) h
