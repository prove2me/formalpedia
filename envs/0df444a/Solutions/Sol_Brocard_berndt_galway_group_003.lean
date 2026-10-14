-- Prove2me | solution 1 for Brocard.berndt_galway_group_003
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:15:16.798932+00:00
-- url     : https://prove2.me/submissions/ed250c7a-6fd3-4041-af98-70276c341c64

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_0095
import Theorems.Thm_Brocard_berndt_galway_chunk_0096
import Theorems.Thm_Brocard_berndt_galway_chunk_0097
import Theorems.Thm_Brocard_berndt_galway_chunk_0098
import Theorems.Thm_Brocard_berndt_galway_chunk_0099
import Theorems.Thm_Brocard_berndt_galway_chunk_0100
import Theorems.Thm_Brocard_berndt_galway_chunk_0101
import Theorems.Thm_Brocard_berndt_galway_chunk_0102
import Theorems.Thm_Brocard_berndt_galway_chunk_0103
import Theorems.Thm_Brocard_berndt_galway_chunk_0104
import Theorems.Thm_Brocard_berndt_galway_chunk_0105
import Theorems.Thm_Brocard_berndt_galway_chunk_0106
import Theorems.Thm_Brocard_berndt_galway_chunk_0107
import Theorems.Thm_Brocard_berndt_galway_chunk_0108
import Theorems.Thm_Brocard_berndt_galway_chunk_0109
import Theorems.Thm_Brocard_berndt_galway_chunk_0110
import Theorems.Thm_Brocard_berndt_galway_chunk_0111
import Theorems.Thm_Brocard_berndt_galway_chunk_0112
import Theorems.Thm_Brocard_berndt_galway_chunk_0113
import Theorems.Thm_Brocard_berndt_galway_chunk_0114
import Theorems.Thm_Brocard_berndt_galway_chunk_0115
import Theorems.Thm_Brocard_berndt_galway_chunk_0116
import Theorems.Thm_Brocard_berndt_galway_chunk_0117
import Theorems.Thm_Brocard_berndt_galway_chunk_0118
import Theorems.Thm_Brocard_berndt_galway_chunk_0119
import Theorems.Thm_Brocard_berndt_galway_chunk_0120
import Theorems.Thm_Brocard_berndt_galway_chunk_0121
import Theorems.Thm_Brocard_berndt_galway_chunk_0122
import Theorems.Thm_Brocard_berndt_galway_chunk_0123
import Theorems.Thm_Brocard_berndt_galway_chunk_0124
import Theorems.Thm_Brocard_berndt_galway_chunk_0125
import Theorems.Thm_Brocard_berndt_galway_chunk_0126
import Theorems.Thm_Brocard_berndt_galway_chunk_0127
import Theorems.Thm_Brocard_berndt_galway_chunk_0128
import Theorems.Thm_Brocard_berndt_galway_chunk_0129
import Theorems.Thm_Brocard_berndt_galway_chunk_0130
import Theorems.Thm_Brocard_berndt_galway_chunk_0131
import Theorems.Thm_Brocard_berndt_galway_chunk_0132
import Theorems.Thm_Brocard_berndt_galway_chunk_0133
import Theorems.Thm_Brocard_berndt_galway_chunk_0134
import Theorems.Thm_Brocard_berndt_galway_chunk_0135
import Theorems.Thm_Brocard_berndt_galway_chunk_0136
import Theorems.Thm_Brocard_berndt_galway_chunk_0137
import Theorems.Thm_Brocard_berndt_galway_chunk_0138
import Theorems.Thm_Brocard_berndt_galway_chunk_0139
import Theorems.Thm_Brocard_berndt_galway_chunk_0140
import Theorems.Thm_Brocard_berndt_galway_chunk_0141

theorem solution (n m : ℕ) (h1 : 16906481 ≤ n) (h2 : n < 25359718) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 21223027 with hs0 | hs0
  · -- n < 21223027
    rcases Nat.lt_or_ge n 19064754 with hs1 | hs1
    · -- n < 19064754
      rcases Nat.lt_or_ge n 17985618 with hs2 | hs2
      · -- n < 17985618
        rcases Nat.lt_or_ge n 17446049 with hs3 | hs3
        · -- n < 17446049
          rcases Nat.lt_or_ge n 17266193 with hs4 | hs4
          · -- n < 17266193
            rcases Nat.lt_or_ge n 17086337 with hs5 | hs5
            · -- n < 17086337
              exact Brocard.berndt_galway_chunk_0095 n m (by omega) (by omega) h
            · -- n >= 17086337
              exact Brocard.berndt_galway_chunk_0096 n m (by omega) (by omega) h
          · -- n >= 17266193
            exact Brocard.berndt_galway_chunk_0097 n m (by omega) (by omega) h
        · -- n >= 17446049
          rcases Nat.lt_or_ge n 17805761 with hs4 | hs4
          · -- n < 17805761
            rcases Nat.lt_or_ge n 17625905 with hs5 | hs5
            · -- n < 17625905
              exact Brocard.berndt_galway_chunk_0098 n m (by omega) (by omega) h
            · -- n >= 17625905
              exact Brocard.berndt_galway_chunk_0099 n m (by omega) (by omega) h
          · -- n >= 17805761
            exact Brocard.berndt_galway_chunk_0100 n m (by omega) (by omega) h
      · -- n >= 17985618
        rcases Nat.lt_or_ge n 18525186 with hs3 | hs3
        · -- n < 18525186
          rcases Nat.lt_or_ge n 18345330 with hs4 | hs4
          · -- n < 18345330
            rcases Nat.lt_or_ge n 18165474 with hs5 | hs5
            · -- n < 18165474
              exact Brocard.berndt_galway_chunk_0101 n m (by omega) (by omega) h
            · -- n >= 18165474
              exact Brocard.berndt_galway_chunk_0102 n m (by omega) (by omega) h
          · -- n >= 18345330
            exact Brocard.berndt_galway_chunk_0103 n m (by omega) (by omega) h
        · -- n >= 18525186
          rcases Nat.lt_or_ge n 18884898 with hs4 | hs4
          · -- n < 18884898
            rcases Nat.lt_or_ge n 18705042 with hs5 | hs5
            · -- n < 18705042
              exact Brocard.berndt_galway_chunk_0104 n m (by omega) (by omega) h
            · -- n >= 18705042
              exact Brocard.berndt_galway_chunk_0105 n m (by omega) (by omega) h
          · -- n >= 18884898
            exact Brocard.berndt_galway_chunk_0106 n m (by omega) (by omega) h
    · -- n >= 19064754
      rcases Nat.lt_or_ge n 20143891 with hs2 | hs2
      · -- n < 20143891
        rcases Nat.lt_or_ge n 19604322 with hs3 | hs3
        · -- n < 19604322
          rcases Nat.lt_or_ge n 19424466 with hs4 | hs4
          · -- n < 19424466
            rcases Nat.lt_or_ge n 19244610 with hs5 | hs5
            · -- n < 19244610
              exact Brocard.berndt_galway_chunk_0107 n m (by omega) (by omega) h
            · -- n >= 19244610
              exact Brocard.berndt_galway_chunk_0108 n m (by omega) (by omega) h
          · -- n >= 19424466
            exact Brocard.berndt_galway_chunk_0109 n m (by omega) (by omega) h
        · -- n >= 19604322
          rcases Nat.lt_or_ge n 19964035 with hs4 | hs4
          · -- n < 19964035
            rcases Nat.lt_or_ge n 19784179 with hs5 | hs5
            · -- n < 19784179
              exact Brocard.berndt_galway_chunk_0110 n m (by omega) (by omega) h
            · -- n >= 19784179
              exact Brocard.berndt_galway_chunk_0111 n m (by omega) (by omega) h
          · -- n >= 19964035
            exact Brocard.berndt_galway_chunk_0112 n m (by omega) (by omega) h
      · -- n >= 20143891
        rcases Nat.lt_or_ge n 20683459 with hs3 | hs3
        · -- n < 20683459
          rcases Nat.lt_or_ge n 20503603 with hs4 | hs4
          · -- n < 20503603
            rcases Nat.lt_or_ge n 20323747 with hs5 | hs5
            · -- n < 20323747
              exact Brocard.berndt_galway_chunk_0113 n m (by omega) (by omega) h
            · -- n >= 20323747
              exact Brocard.berndt_galway_chunk_0114 n m (by omega) (by omega) h
          · -- n >= 20503603
            exact Brocard.berndt_galway_chunk_0115 n m (by omega) (by omega) h
        · -- n >= 20683459
          rcases Nat.lt_or_ge n 21043171 with hs4 | hs4
          · -- n < 21043171
            rcases Nat.lt_or_ge n 20863315 with hs5 | hs5
            · -- n < 20863315
              exact Brocard.berndt_galway_chunk_0116 n m (by omega) (by omega) h
            · -- n >= 20863315
              exact Brocard.berndt_galway_chunk_0117 n m (by omega) (by omega) h
          · -- n >= 21043171
            exact Brocard.berndt_galway_chunk_0118 n m (by omega) (by omega) h
  · -- n >= 21223027
    rcases Nat.lt_or_ge n 23381301 with hs1 | hs1
    · -- n < 23381301
      rcases Nat.lt_or_ge n 22302164 with hs2 | hs2
      · -- n < 22302164
        rcases Nat.lt_or_ge n 21762596 with hs3 | hs3
        · -- n < 21762596
          rcases Nat.lt_or_ge n 21582740 with hs4 | hs4
          · -- n < 21582740
            rcases Nat.lt_or_ge n 21402883 with hs5 | hs5
            · -- n < 21402883
              exact Brocard.berndt_galway_chunk_0119 n m (by omega) (by omega) h
            · -- n >= 21402883
              exact Brocard.berndt_galway_chunk_0120 n m (by omega) (by omega) h
          · -- n >= 21582740
            exact Brocard.berndt_galway_chunk_0121 n m (by omega) (by omega) h
        · -- n >= 21762596
          rcases Nat.lt_or_ge n 22122308 with hs4 | hs4
          · -- n < 22122308
            rcases Nat.lt_or_ge n 21942452 with hs5 | hs5
            · -- n < 21942452
              exact Brocard.berndt_galway_chunk_0122 n m (by omega) (by omega) h
            · -- n >= 21942452
              exact Brocard.berndt_galway_chunk_0123 n m (by omega) (by omega) h
          · -- n >= 22122308
            exact Brocard.berndt_galway_chunk_0124 n m (by omega) (by omega) h
      · -- n >= 22302164
        rcases Nat.lt_or_ge n 22841732 with hs3 | hs3
        · -- n < 22841732
          rcases Nat.lt_or_ge n 22661876 with hs4 | hs4
          · -- n < 22661876
            rcases Nat.lt_or_ge n 22482020 with hs5 | hs5
            · -- n < 22482020
              exact Brocard.berndt_galway_chunk_0125 n m (by omega) (by omega) h
            · -- n >= 22482020
              exact Brocard.berndt_galway_chunk_0126 n m (by omega) (by omega) h
          · -- n >= 22661876
            exact Brocard.berndt_galway_chunk_0127 n m (by omega) (by omega) h
        · -- n >= 22841732
          rcases Nat.lt_or_ge n 23201444 with hs4 | hs4
          · -- n < 23201444
            rcases Nat.lt_or_ge n 23021588 with hs5 | hs5
            · -- n < 23021588
              exact Brocard.berndt_galway_chunk_0128 n m (by omega) (by omega) h
            · -- n >= 23021588
              exact Brocard.berndt_galway_chunk_0129 n m (by omega) (by omega) h
          · -- n >= 23201444
            exact Brocard.berndt_galway_chunk_0130 n m (by omega) (by omega) h
    · -- n >= 23381301
      rcases Nat.lt_or_ge n 24460437 with hs2 | hs2
      · -- n < 24460437
        rcases Nat.lt_or_ge n 23920869 with hs3 | hs3
        · -- n < 23920869
          rcases Nat.lt_or_ge n 23741013 with hs4 | hs4
          · -- n < 23741013
            rcases Nat.lt_or_ge n 23561157 with hs5 | hs5
            · -- n < 23561157
              exact Brocard.berndt_galway_chunk_0131 n m (by omega) (by omega) h
            · -- n >= 23561157
              exact Brocard.berndt_galway_chunk_0132 n m (by omega) (by omega) h
          · -- n >= 23741013
            exact Brocard.berndt_galway_chunk_0133 n m (by omega) (by omega) h
        · -- n >= 23920869
          rcases Nat.lt_or_ge n 24280581 with hs4 | hs4
          · -- n < 24280581
            rcases Nat.lt_or_ge n 24100725 with hs5 | hs5
            · -- n < 24100725
              exact Brocard.berndt_galway_chunk_0134 n m (by omega) (by omega) h
            · -- n >= 24100725
              exact Brocard.berndt_galway_chunk_0135 n m (by omega) (by omega) h
          · -- n >= 24280581
            exact Brocard.berndt_galway_chunk_0136 n m (by omega) (by omega) h
      · -- n >= 24460437
        rcases Nat.lt_or_ge n 25000006 with hs3 | hs3
        · -- n < 25000006
          rcases Nat.lt_or_ge n 24820149 with hs4 | hs4
          · -- n < 24820149
            rcases Nat.lt_or_ge n 24640293 with hs5 | hs5
            · -- n < 24640293
              exact Brocard.berndt_galway_chunk_0137 n m (by omega) (by omega) h
            · -- n >= 24640293
              exact Brocard.berndt_galway_chunk_0138 n m (by omega) (by omega) h
          · -- n >= 24820149
            exact Brocard.berndt_galway_chunk_0139 n m (by omega) (by omega) h
        · -- n >= 25000006
          rcases Nat.lt_or_ge n 25179862 with hs4 | hs4
          · -- n < 25179862
            exact Brocard.berndt_galway_chunk_0140 n m (by omega) (by omega) h
          · -- n >= 25179862
            exact Brocard.berndt_galway_chunk_0141 n m (by omega) (by omega) h
