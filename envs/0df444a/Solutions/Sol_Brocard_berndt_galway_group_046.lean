-- Prove2me | solution 1 for Brocard.berndt_galway_group_046
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:53:52.329614+00:00
-- url     : https://prove2.me/submissions/709b7596-74fb-4d7a-aad6-92b7c4ac87ae

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_2087
import Theorems.Thm_Brocard_berndt_galway_chunk_2088
import Theorems.Thm_Brocard_berndt_galway_chunk_2089
import Theorems.Thm_Brocard_berndt_galway_chunk_2090
import Theorems.Thm_Brocard_berndt_galway_chunk_2091
import Theorems.Thm_Brocard_berndt_galway_chunk_2092
import Theorems.Thm_Brocard_berndt_galway_chunk_2093
import Theorems.Thm_Brocard_berndt_galway_chunk_2094
import Theorems.Thm_Brocard_berndt_galway_chunk_2095
import Theorems.Thm_Brocard_berndt_galway_chunk_2096
import Theorems.Thm_Brocard_berndt_galway_chunk_2097
import Theorems.Thm_Brocard_berndt_galway_chunk_2098
import Theorems.Thm_Brocard_berndt_galway_chunk_2099
import Theorems.Thm_Brocard_berndt_galway_chunk_2100
import Theorems.Thm_Brocard_berndt_galway_chunk_2101
import Theorems.Thm_Brocard_berndt_galway_chunk_2102
import Theorems.Thm_Brocard_berndt_galway_chunk_2103
import Theorems.Thm_Brocard_berndt_galway_chunk_2104
import Theorems.Thm_Brocard_berndt_galway_chunk_2105
import Theorems.Thm_Brocard_berndt_galway_chunk_2106
import Theorems.Thm_Brocard_berndt_galway_chunk_2107
import Theorems.Thm_Brocard_berndt_galway_chunk_2108
import Theorems.Thm_Brocard_berndt_galway_chunk_2109
import Theorems.Thm_Brocard_berndt_galway_chunk_2110
import Theorems.Thm_Brocard_berndt_galway_chunk_2111
import Theorems.Thm_Brocard_berndt_galway_chunk_2112
import Theorems.Thm_Brocard_berndt_galway_chunk_2113
import Theorems.Thm_Brocard_berndt_galway_chunk_2114
import Theorems.Thm_Brocard_berndt_galway_chunk_2115
import Theorems.Thm_Brocard_berndt_galway_chunk_2116
import Theorems.Thm_Brocard_berndt_galway_chunk_2117
import Theorems.Thm_Brocard_berndt_galway_chunk_2118
import Theorems.Thm_Brocard_berndt_galway_chunk_2119
import Theorems.Thm_Brocard_berndt_galway_chunk_2120
import Theorems.Thm_Brocard_berndt_galway_chunk_2121
import Theorems.Thm_Brocard_berndt_galway_chunk_2122
import Theorems.Thm_Brocard_berndt_galway_chunk_2123
import Theorems.Thm_Brocard_berndt_galway_chunk_2124
import Theorems.Thm_Brocard_berndt_galway_chunk_2125
import Theorems.Thm_Brocard_berndt_galway_chunk_2126
import Theorems.Thm_Brocard_berndt_galway_chunk_2127
import Theorems.Thm_Brocard_berndt_galway_chunk_2128
import Theorems.Thm_Brocard_berndt_galway_chunk_2129
import Theorems.Thm_Brocard_berndt_galway_chunk_2130
import Theorems.Thm_Brocard_berndt_galway_chunk_2131
import Theorems.Thm_Brocard_berndt_galway_chunk_2132

theorem solution (n m : ℕ) (h1 : 375179856 ≤ n) (h2 : n < 383453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 379316546 with hs0 | hs0
  · -- n < 379316546
    rcases Nat.lt_or_ge n 377338129 with hs1 | hs1
    · -- n < 377338129
      rcases Nat.lt_or_ge n 376258992 with hs2 | hs2
      · -- n < 376258992
        rcases Nat.lt_or_ge n 375719424 with hs3 | hs3
        · -- n < 375719424
          rcases Nat.lt_or_ge n 375539568 with hs4 | hs4
          · -- n < 375539568
            rcases Nat.lt_or_ge n 375359712 with hs5 | hs5
            · -- n < 375359712
              exact Brocard.berndt_galway_chunk_2087 n m (by omega) (by omega) h
            · -- n >= 375359712
              exact Brocard.berndt_galway_chunk_2088 n m (by omega) (by omega) h
          · -- n >= 375539568
            exact Brocard.berndt_galway_chunk_2089 n m (by omega) (by omega) h
        · -- n >= 375719424
          rcases Nat.lt_or_ge n 376079136 with hs4 | hs4
          · -- n < 376079136
            rcases Nat.lt_or_ge n 375899280 with hs5 | hs5
            · -- n < 375899280
              exact Brocard.berndt_galway_chunk_2090 n m (by omega) (by omega) h
            · -- n >= 375899280
              exact Brocard.berndt_galway_chunk_2091 n m (by omega) (by omega) h
          · -- n >= 376079136
            exact Brocard.berndt_galway_chunk_2092 n m (by omega) (by omega) h
      · -- n >= 376258992
        rcases Nat.lt_or_ge n 376798561 with hs3 | hs3
        · -- n < 376798561
          rcases Nat.lt_or_ge n 376618705 with hs4 | hs4
          · -- n < 376618705
            rcases Nat.lt_or_ge n 376438848 with hs5 | hs5
            · -- n < 376438848
              exact Brocard.berndt_galway_chunk_2093 n m (by omega) (by omega) h
            · -- n >= 376438848
              exact Brocard.berndt_galway_chunk_2094 n m (by omega) (by omega) h
          · -- n >= 376618705
            exact Brocard.berndt_galway_chunk_2095 n m (by omega) (by omega) h
        · -- n >= 376798561
          rcases Nat.lt_or_ge n 377158273 with hs4 | hs4
          · -- n < 377158273
            rcases Nat.lt_or_ge n 376978417 with hs5 | hs5
            · -- n < 376978417
              exact Brocard.berndt_galway_chunk_2096 n m (by omega) (by omega) h
            · -- n >= 376978417
              exact Brocard.berndt_galway_chunk_2097 n m (by omega) (by omega) h
          · -- n >= 377158273
            exact Brocard.berndt_galway_chunk_2098 n m (by omega) (by omega) h
    · -- n >= 377338129
      rcases Nat.lt_or_ge n 378417266 with hs2 | hs2
      · -- n < 378417266
        rcases Nat.lt_or_ge n 377877697 with hs3 | hs3
        · -- n < 377877697
          rcases Nat.lt_or_ge n 377697841 with hs4 | hs4
          · -- n < 377697841
            rcases Nat.lt_or_ge n 377517985 with hs5 | hs5
            · -- n < 377517985
              exact Brocard.berndt_galway_chunk_2099 n m (by omega) (by omega) h
            · -- n >= 377517985
              exact Brocard.berndt_galway_chunk_2100 n m (by omega) (by omega) h
          · -- n >= 377697841
            exact Brocard.berndt_galway_chunk_2101 n m (by omega) (by omega) h
        · -- n >= 377877697
          rcases Nat.lt_or_ge n 378237410 with hs4 | hs4
          · -- n < 378237410
            rcases Nat.lt_or_ge n 378057553 with hs5 | hs5
            · -- n < 378057553
              exact Brocard.berndt_galway_chunk_2102 n m (by omega) (by omega) h
            · -- n >= 378057553
              exact Brocard.berndt_galway_chunk_2103 n m (by omega) (by omega) h
          · -- n >= 378237410
            exact Brocard.berndt_galway_chunk_2104 n m (by omega) (by omega) h
      · -- n >= 378417266
        rcases Nat.lt_or_ge n 378956834 with hs3 | hs3
        · -- n < 378956834
          rcases Nat.lt_or_ge n 378776978 with hs4 | hs4
          · -- n < 378776978
            rcases Nat.lt_or_ge n 378597122 with hs5 | hs5
            · -- n < 378597122
              exact Brocard.berndt_galway_chunk_2105 n m (by omega) (by omega) h
            · -- n >= 378597122
              exact Brocard.berndt_galway_chunk_2106 n m (by omega) (by omega) h
          · -- n >= 378776978
            exact Brocard.berndt_galway_chunk_2107 n m (by omega) (by omega) h
        · -- n >= 378956834
          rcases Nat.lt_or_ge n 379136690 with hs4 | hs4
          · -- n < 379136690
            exact Brocard.berndt_galway_chunk_2108 n m (by omega) (by omega) h
          · -- n >= 379136690
            exact Brocard.berndt_galway_chunk_2109 n m (by omega) (by omega) h
  · -- n >= 379316546
    rcases Nat.lt_or_ge n 381474820 with hs1 | hs1
    · -- n < 381474820
      rcases Nat.lt_or_ge n 380395683 with hs2 | hs2
      · -- n < 380395683
        rcases Nat.lt_or_ge n 379856115 with hs3 | hs3
        · -- n < 379856115
          rcases Nat.lt_or_ge n 379676258 with hs4 | hs4
          · -- n < 379676258
            rcases Nat.lt_or_ge n 379496402 with hs5 | hs5
            · -- n < 379496402
              exact Brocard.berndt_galway_chunk_2110 n m (by omega) (by omega) h
            · -- n >= 379496402
              exact Brocard.berndt_galway_chunk_2111 n m (by omega) (by omega) h
          · -- n >= 379676258
            exact Brocard.berndt_galway_chunk_2112 n m (by omega) (by omega) h
        · -- n >= 379856115
          rcases Nat.lt_or_ge n 380215827 with hs4 | hs4
          · -- n < 380215827
            rcases Nat.lt_or_ge n 380035971 with hs5 | hs5
            · -- n < 380035971
              exact Brocard.berndt_galway_chunk_2113 n m (by omega) (by omega) h
            · -- n >= 380035971
              exact Brocard.berndt_galway_chunk_2114 n m (by omega) (by omega) h
          · -- n >= 380215827
            exact Brocard.berndt_galway_chunk_2115 n m (by omega) (by omega) h
      · -- n >= 380395683
        rcases Nat.lt_or_ge n 380935251 with hs3 | hs3
        · -- n < 380935251
          rcases Nat.lt_or_ge n 380755395 with hs4 | hs4
          · -- n < 380755395
            rcases Nat.lt_or_ge n 380575539 with hs5 | hs5
            · -- n < 380575539
              exact Brocard.berndt_galway_chunk_2116 n m (by omega) (by omega) h
            · -- n >= 380575539
              exact Brocard.berndt_galway_chunk_2117 n m (by omega) (by omega) h
          · -- n >= 380755395
            exact Brocard.berndt_galway_chunk_2118 n m (by omega) (by omega) h
        · -- n >= 380935251
          rcases Nat.lt_or_ge n 381294964 with hs4 | hs4
          · -- n < 381294964
            rcases Nat.lt_or_ge n 381115107 with hs5 | hs5
            · -- n < 381115107
              exact Brocard.berndt_galway_chunk_2119 n m (by omega) (by omega) h
            · -- n >= 381115107
              exact Brocard.berndt_galway_chunk_2120 n m (by omega) (by omega) h
          · -- n >= 381294964
            exact Brocard.berndt_galway_chunk_2121 n m (by omega) (by omega) h
    · -- n >= 381474820
      rcases Nat.lt_or_ge n 382553956 with hs2 | hs2
      · -- n < 382553956
        rcases Nat.lt_or_ge n 382014388 with hs3 | hs3
        · -- n < 382014388
          rcases Nat.lt_or_ge n 381834532 with hs4 | hs4
          · -- n < 381834532
            rcases Nat.lt_or_ge n 381654676 with hs5 | hs5
            · -- n < 381654676
              exact Brocard.berndt_galway_chunk_2122 n m (by omega) (by omega) h
            · -- n >= 381654676
              exact Brocard.berndt_galway_chunk_2123 n m (by omega) (by omega) h
          · -- n >= 381834532
            exact Brocard.berndt_galway_chunk_2124 n m (by omega) (by omega) h
        · -- n >= 382014388
          rcases Nat.lt_or_ge n 382374100 with hs4 | hs4
          · -- n < 382374100
            rcases Nat.lt_or_ge n 382194244 with hs5 | hs5
            · -- n < 382194244
              exact Brocard.berndt_galway_chunk_2125 n m (by omega) (by omega) h
            · -- n >= 382194244
              exact Brocard.berndt_galway_chunk_2126 n m (by omega) (by omega) h
          · -- n >= 382374100
            exact Brocard.berndt_galway_chunk_2127 n m (by omega) (by omega) h
      · -- n >= 382553956
        rcases Nat.lt_or_ge n 383093525 with hs3 | hs3
        · -- n < 383093525
          rcases Nat.lt_or_ge n 382913669 with hs4 | hs4
          · -- n < 382913669
            rcases Nat.lt_or_ge n 382733812 with hs5 | hs5
            · -- n < 382733812
              exact Brocard.berndt_galway_chunk_2128 n m (by omega) (by omega) h
            · -- n >= 382733812
              exact Brocard.berndt_galway_chunk_2129 n m (by omega) (by omega) h
          · -- n >= 382913669
            exact Brocard.berndt_galway_chunk_2130 n m (by omega) (by omega) h
        · -- n >= 383093525
          rcases Nat.lt_or_ge n 383273381 with hs4 | hs4
          · -- n < 383273381
            exact Brocard.berndt_galway_chunk_2131 n m (by omega) (by omega) h
          · -- n >= 383273381
            exact Brocard.berndt_galway_chunk_2132 n m (by omega) (by omega) h
