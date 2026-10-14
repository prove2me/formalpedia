-- Prove2me | solution 1 for Brocard.berndt_galway_group_067
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:50:39.924897+00:00
-- url     : https://prove2.me/submissions/eaa4141d-04f7-4d8c-8501-ccc399c9e662

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_3061
import Theorems.Thm_Brocard_berndt_galway_chunk_3062
import Theorems.Thm_Brocard_berndt_galway_chunk_3063
import Theorems.Thm_Brocard_berndt_galway_chunk_3064
import Theorems.Thm_Brocard_berndt_galway_chunk_3065
import Theorems.Thm_Brocard_berndt_galway_chunk_3066
import Theorems.Thm_Brocard_berndt_galway_chunk_3067
import Theorems.Thm_Brocard_berndt_galway_chunk_3068
import Theorems.Thm_Brocard_berndt_galway_chunk_3069
import Theorems.Thm_Brocard_berndt_galway_chunk_3070
import Theorems.Thm_Brocard_berndt_galway_chunk_3071
import Theorems.Thm_Brocard_berndt_galway_chunk_3072
import Theorems.Thm_Brocard_berndt_galway_chunk_3073
import Theorems.Thm_Brocard_berndt_galway_chunk_3074
import Theorems.Thm_Brocard_berndt_galway_chunk_3075
import Theorems.Thm_Brocard_berndt_galway_chunk_3076
import Theorems.Thm_Brocard_berndt_galway_chunk_3077
import Theorems.Thm_Brocard_berndt_galway_chunk_3078
import Theorems.Thm_Brocard_berndt_galway_chunk_3079
import Theorems.Thm_Brocard_berndt_galway_chunk_3080
import Theorems.Thm_Brocard_berndt_galway_chunk_3081
import Theorems.Thm_Brocard_berndt_galway_chunk_3082
import Theorems.Thm_Brocard_berndt_galway_chunk_3083
import Theorems.Thm_Brocard_berndt_galway_chunk_3084
import Theorems.Thm_Brocard_berndt_galway_chunk_3085
import Theorems.Thm_Brocard_berndt_galway_chunk_3086
import Theorems.Thm_Brocard_berndt_galway_chunk_3087
import Theorems.Thm_Brocard_berndt_galway_chunk_3088
import Theorems.Thm_Brocard_berndt_galway_chunk_3089
import Theorems.Thm_Brocard_berndt_galway_chunk_3090
import Theorems.Thm_Brocard_berndt_galway_chunk_3091
import Theorems.Thm_Brocard_berndt_galway_chunk_3092
import Theorems.Thm_Brocard_berndt_galway_chunk_3093
import Theorems.Thm_Brocard_berndt_galway_chunk_3094
import Theorems.Thm_Brocard_berndt_galway_chunk_3095
import Theorems.Thm_Brocard_berndt_galway_chunk_3096
import Theorems.Thm_Brocard_berndt_galway_chunk_3097
import Theorems.Thm_Brocard_berndt_galway_chunk_3098
import Theorems.Thm_Brocard_berndt_galway_chunk_3099
import Theorems.Thm_Brocard_berndt_galway_chunk_3100
import Theorems.Thm_Brocard_berndt_galway_chunk_3101
import Theorems.Thm_Brocard_berndt_galway_chunk_3102
import Theorems.Thm_Brocard_berndt_galway_chunk_3103
import Theorems.Thm_Brocard_berndt_galway_chunk_3104
import Theorems.Thm_Brocard_berndt_galway_chunk_3105
import Theorems.Thm_Brocard_berndt_galway_chunk_3106

theorem solution (n m : ℕ) (h1 : 550359712 ≤ n) (h2 : n < 558633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 554496402 with hs0 | hs0
  · -- n < 554496402
    rcases Nat.lt_or_ge n 552517985 with hs1 | hs1
    · -- n < 552517985
      rcases Nat.lt_or_ge n 551438848 with hs2 | hs2
      · -- n < 551438848
        rcases Nat.lt_or_ge n 550899280 with hs3 | hs3
        · -- n < 550899280
          rcases Nat.lt_or_ge n 550719424 with hs4 | hs4
          · -- n < 550719424
            rcases Nat.lt_or_ge n 550539568 with hs5 | hs5
            · -- n < 550539568
              exact Brocard.berndt_galway_chunk_3061 n m (by omega) (by omega) h
            · -- n >= 550539568
              exact Brocard.berndt_galway_chunk_3062 n m (by omega) (by omega) h
          · -- n >= 550719424
            exact Brocard.berndt_galway_chunk_3063 n m (by omega) (by omega) h
        · -- n >= 550899280
          rcases Nat.lt_or_ge n 551258992 with hs4 | hs4
          · -- n < 551258992
            rcases Nat.lt_or_ge n 551079136 with hs5 | hs5
            · -- n < 551079136
              exact Brocard.berndt_galway_chunk_3064 n m (by omega) (by omega) h
            · -- n >= 551079136
              exact Brocard.berndt_galway_chunk_3065 n m (by omega) (by omega) h
          · -- n >= 551258992
            exact Brocard.berndt_galway_chunk_3066 n m (by omega) (by omega) h
      · -- n >= 551438848
        rcases Nat.lt_or_ge n 551978417 with hs3 | hs3
        · -- n < 551978417
          rcases Nat.lt_or_ge n 551798561 with hs4 | hs4
          · -- n < 551798561
            rcases Nat.lt_or_ge n 551618705 with hs5 | hs5
            · -- n < 551618705
              exact Brocard.berndt_galway_chunk_3067 n m (by omega) (by omega) h
            · -- n >= 551618705
              exact Brocard.berndt_galway_chunk_3068 n m (by omega) (by omega) h
          · -- n >= 551798561
            exact Brocard.berndt_galway_chunk_3069 n m (by omega) (by omega) h
        · -- n >= 551978417
          rcases Nat.lt_or_ge n 552338129 with hs4 | hs4
          · -- n < 552338129
            rcases Nat.lt_or_ge n 552158273 with hs5 | hs5
            · -- n < 552158273
              exact Brocard.berndt_galway_chunk_3070 n m (by omega) (by omega) h
            · -- n >= 552158273
              exact Brocard.berndt_galway_chunk_3071 n m (by omega) (by omega) h
          · -- n >= 552338129
            exact Brocard.berndt_galway_chunk_3072 n m (by omega) (by omega) h
    · -- n >= 552517985
      rcases Nat.lt_or_ge n 553597122 with hs2 | hs2
      · -- n < 553597122
        rcases Nat.lt_or_ge n 553057553 with hs3 | hs3
        · -- n < 553057553
          rcases Nat.lt_or_ge n 552877697 with hs4 | hs4
          · -- n < 552877697
            rcases Nat.lt_or_ge n 552697841 with hs5 | hs5
            · -- n < 552697841
              exact Brocard.berndt_galway_chunk_3073 n m (by omega) (by omega) h
            · -- n >= 552697841
              exact Brocard.berndt_galway_chunk_3074 n m (by omega) (by omega) h
          · -- n >= 552877697
            exact Brocard.berndt_galway_chunk_3075 n m (by omega) (by omega) h
        · -- n >= 553057553
          rcases Nat.lt_or_ge n 553417266 with hs4 | hs4
          · -- n < 553417266
            rcases Nat.lt_or_ge n 553237410 with hs5 | hs5
            · -- n < 553237410
              exact Brocard.berndt_galway_chunk_3076 n m (by omega) (by omega) h
            · -- n >= 553237410
              exact Brocard.berndt_galway_chunk_3077 n m (by omega) (by omega) h
          · -- n >= 553417266
            exact Brocard.berndt_galway_chunk_3078 n m (by omega) (by omega) h
      · -- n >= 553597122
        rcases Nat.lt_or_ge n 554136690 with hs3 | hs3
        · -- n < 554136690
          rcases Nat.lt_or_ge n 553956834 with hs4 | hs4
          · -- n < 553956834
            rcases Nat.lt_or_ge n 553776978 with hs5 | hs5
            · -- n < 553776978
              exact Brocard.berndt_galway_chunk_3079 n m (by omega) (by omega) h
            · -- n >= 553776978
              exact Brocard.berndt_galway_chunk_3080 n m (by omega) (by omega) h
          · -- n >= 553956834
            exact Brocard.berndt_galway_chunk_3081 n m (by omega) (by omega) h
        · -- n >= 554136690
          rcases Nat.lt_or_ge n 554316546 with hs4 | hs4
          · -- n < 554316546
            exact Brocard.berndt_galway_chunk_3082 n m (by omega) (by omega) h
          · -- n >= 554316546
            exact Brocard.berndt_galway_chunk_3083 n m (by omega) (by omega) h
  · -- n >= 554496402
    rcases Nat.lt_or_ge n 556654676 with hs1 | hs1
    · -- n < 556654676
      rcases Nat.lt_or_ge n 555575539 with hs2 | hs2
      · -- n < 555575539
        rcases Nat.lt_or_ge n 555035971 with hs3 | hs3
        · -- n < 555035971
          rcases Nat.lt_or_ge n 554856115 with hs4 | hs4
          · -- n < 554856115
            rcases Nat.lt_or_ge n 554676258 with hs5 | hs5
            · -- n < 554676258
              exact Brocard.berndt_galway_chunk_3084 n m (by omega) (by omega) h
            · -- n >= 554676258
              exact Brocard.berndt_galway_chunk_3085 n m (by omega) (by omega) h
          · -- n >= 554856115
            exact Brocard.berndt_galway_chunk_3086 n m (by omega) (by omega) h
        · -- n >= 555035971
          rcases Nat.lt_or_ge n 555395683 with hs4 | hs4
          · -- n < 555395683
            rcases Nat.lt_or_ge n 555215827 with hs5 | hs5
            · -- n < 555215827
              exact Brocard.berndt_galway_chunk_3087 n m (by omega) (by omega) h
            · -- n >= 555215827
              exact Brocard.berndt_galway_chunk_3088 n m (by omega) (by omega) h
          · -- n >= 555395683
            exact Brocard.berndt_galway_chunk_3089 n m (by omega) (by omega) h
      · -- n >= 555575539
        rcases Nat.lt_or_ge n 556115107 with hs3 | hs3
        · -- n < 556115107
          rcases Nat.lt_or_ge n 555935251 with hs4 | hs4
          · -- n < 555935251
            rcases Nat.lt_or_ge n 555755395 with hs5 | hs5
            · -- n < 555755395
              exact Brocard.berndt_galway_chunk_3090 n m (by omega) (by omega) h
            · -- n >= 555755395
              exact Brocard.berndt_galway_chunk_3091 n m (by omega) (by omega) h
          · -- n >= 555935251
            exact Brocard.berndt_galway_chunk_3092 n m (by omega) (by omega) h
        · -- n >= 556115107
          rcases Nat.lt_or_ge n 556474820 with hs4 | hs4
          · -- n < 556474820
            rcases Nat.lt_or_ge n 556294964 with hs5 | hs5
            · -- n < 556294964
              exact Brocard.berndt_galway_chunk_3093 n m (by omega) (by omega) h
            · -- n >= 556294964
              exact Brocard.berndt_galway_chunk_3094 n m (by omega) (by omega) h
          · -- n >= 556474820
            exact Brocard.berndt_galway_chunk_3095 n m (by omega) (by omega) h
    · -- n >= 556654676
      rcases Nat.lt_or_ge n 557733812 with hs2 | hs2
      · -- n < 557733812
        rcases Nat.lt_or_ge n 557194244 with hs3 | hs3
        · -- n < 557194244
          rcases Nat.lt_or_ge n 557014388 with hs4 | hs4
          · -- n < 557014388
            rcases Nat.lt_or_ge n 556834532 with hs5 | hs5
            · -- n < 556834532
              exact Brocard.berndt_galway_chunk_3096 n m (by omega) (by omega) h
            · -- n >= 556834532
              exact Brocard.berndt_galway_chunk_3097 n m (by omega) (by omega) h
          · -- n >= 557014388
            exact Brocard.berndt_galway_chunk_3098 n m (by omega) (by omega) h
        · -- n >= 557194244
          rcases Nat.lt_or_ge n 557553956 with hs4 | hs4
          · -- n < 557553956
            rcases Nat.lt_or_ge n 557374100 with hs5 | hs5
            · -- n < 557374100
              exact Brocard.berndt_galway_chunk_3099 n m (by omega) (by omega) h
            · -- n >= 557374100
              exact Brocard.berndt_galway_chunk_3100 n m (by omega) (by omega) h
          · -- n >= 557553956
            exact Brocard.berndt_galway_chunk_3101 n m (by omega) (by omega) h
      · -- n >= 557733812
        rcases Nat.lt_or_ge n 558273381 with hs3 | hs3
        · -- n < 558273381
          rcases Nat.lt_or_ge n 558093525 with hs4 | hs4
          · -- n < 558093525
            rcases Nat.lt_or_ge n 557913669 with hs5 | hs5
            · -- n < 557913669
              exact Brocard.berndt_galway_chunk_3102 n m (by omega) (by omega) h
            · -- n >= 557913669
              exact Brocard.berndt_galway_chunk_3103 n m (by omega) (by omega) h
          · -- n >= 558093525
            exact Brocard.berndt_galway_chunk_3104 n m (by omega) (by omega) h
        · -- n >= 558273381
          rcases Nat.lt_or_ge n 558453237 with hs4 | hs4
          · -- n < 558453237
            exact Brocard.berndt_galway_chunk_3105 n m (by omega) (by omega) h
          · -- n >= 558453237
            exact Brocard.berndt_galway_chunk_3106 n m (by omega) (by omega) h
