-- Prove2me | solution 1 for Brocard.berndt_galway_group_025
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:37:52.07501+00:00
-- url     : https://prove2.me/submissions/055048fa-8700-4a05-a681-6e1ad508e2f9

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_1113
import Theorems.Thm_Brocard_berndt_galway_chunk_1114
import Theorems.Thm_Brocard_berndt_galway_chunk_1115
import Theorems.Thm_Brocard_berndt_galway_chunk_1116
import Theorems.Thm_Brocard_berndt_galway_chunk_1117
import Theorems.Thm_Brocard_berndt_galway_chunk_1118
import Theorems.Thm_Brocard_berndt_galway_chunk_1119
import Theorems.Thm_Brocard_berndt_galway_chunk_1120
import Theorems.Thm_Brocard_berndt_galway_chunk_1121
import Theorems.Thm_Brocard_berndt_galway_chunk_1122
import Theorems.Thm_Brocard_berndt_galway_chunk_1123
import Theorems.Thm_Brocard_berndt_galway_chunk_1124
import Theorems.Thm_Brocard_berndt_galway_chunk_1125
import Theorems.Thm_Brocard_berndt_galway_chunk_1126
import Theorems.Thm_Brocard_berndt_galway_chunk_1127
import Theorems.Thm_Brocard_berndt_galway_chunk_1128
import Theorems.Thm_Brocard_berndt_galway_chunk_1129
import Theorems.Thm_Brocard_berndt_galway_chunk_1130
import Theorems.Thm_Brocard_berndt_galway_chunk_1131
import Theorems.Thm_Brocard_berndt_galway_chunk_1132
import Theorems.Thm_Brocard_berndt_galway_chunk_1133
import Theorems.Thm_Brocard_berndt_galway_chunk_1134
import Theorems.Thm_Brocard_berndt_galway_chunk_1135
import Theorems.Thm_Brocard_berndt_galway_chunk_1136
import Theorems.Thm_Brocard_berndt_galway_chunk_1137
import Theorems.Thm_Brocard_berndt_galway_chunk_1138
import Theorems.Thm_Brocard_berndt_galway_chunk_1139
import Theorems.Thm_Brocard_berndt_galway_chunk_1140
import Theorems.Thm_Brocard_berndt_galway_chunk_1141
import Theorems.Thm_Brocard_berndt_galway_chunk_1142
import Theorems.Thm_Brocard_berndt_galway_chunk_1143
import Theorems.Thm_Brocard_berndt_galway_chunk_1144
import Theorems.Thm_Brocard_berndt_galway_chunk_1145
import Theorems.Thm_Brocard_berndt_galway_chunk_1146
import Theorems.Thm_Brocard_berndt_galway_chunk_1147
import Theorems.Thm_Brocard_berndt_galway_chunk_1148
import Theorems.Thm_Brocard_berndt_galway_chunk_1149
import Theorems.Thm_Brocard_berndt_galway_chunk_1150
import Theorems.Thm_Brocard_berndt_galway_chunk_1151
import Theorems.Thm_Brocard_berndt_galway_chunk_1152
import Theorems.Thm_Brocard_berndt_galway_chunk_1153
import Theorems.Thm_Brocard_berndt_galway_chunk_1154
import Theorems.Thm_Brocard_berndt_galway_chunk_1155
import Theorems.Thm_Brocard_berndt_galway_chunk_1156
import Theorems.Thm_Brocard_berndt_galway_chunk_1157
import Theorems.Thm_Brocard_berndt_galway_chunk_1158
import Theorems.Thm_Brocard_berndt_galway_chunk_1159

theorem solution (n m : ℕ) (h1 : 200000000 ≤ n) (h2 : n < 208453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 204316546 with hs0 | hs0
  · -- n < 204316546
    rcases Nat.lt_or_ge n 202158273 with hs1 | hs1
    · -- n < 202158273
      rcases Nat.lt_or_ge n 201079136 with hs2 | hs2
      · -- n < 201079136
        rcases Nat.lt_or_ge n 200539568 with hs3 | hs3
        · -- n < 200539568
          rcases Nat.lt_or_ge n 200359712 with hs4 | hs4
          · -- n < 200359712
            rcases Nat.lt_or_ge n 200179856 with hs5 | hs5
            · -- n < 200179856
              exact Brocard.berndt_galway_chunk_1113 n m (by omega) (by omega) h
            · -- n >= 200179856
              exact Brocard.berndt_galway_chunk_1114 n m (by omega) (by omega) h
          · -- n >= 200359712
            exact Brocard.berndt_galway_chunk_1115 n m (by omega) (by omega) h
        · -- n >= 200539568
          rcases Nat.lt_or_ge n 200899280 with hs4 | hs4
          · -- n < 200899280
            rcases Nat.lt_or_ge n 200719424 with hs5 | hs5
            · -- n < 200719424
              exact Brocard.berndt_galway_chunk_1116 n m (by omega) (by omega) h
            · -- n >= 200719424
              exact Brocard.berndt_galway_chunk_1117 n m (by omega) (by omega) h
          · -- n >= 200899280
            exact Brocard.berndt_galway_chunk_1118 n m (by omega) (by omega) h
      · -- n >= 201079136
        rcases Nat.lt_or_ge n 201618705 with hs3 | hs3
        · -- n < 201618705
          rcases Nat.lt_or_ge n 201438848 with hs4 | hs4
          · -- n < 201438848
            rcases Nat.lt_or_ge n 201258992 with hs5 | hs5
            · -- n < 201258992
              exact Brocard.berndt_galway_chunk_1119 n m (by omega) (by omega) h
            · -- n >= 201258992
              exact Brocard.berndt_galway_chunk_1120 n m (by omega) (by omega) h
          · -- n >= 201438848
            exact Brocard.berndt_galway_chunk_1121 n m (by omega) (by omega) h
        · -- n >= 201618705
          rcases Nat.lt_or_ge n 201978417 with hs4 | hs4
          · -- n < 201978417
            rcases Nat.lt_or_ge n 201798561 with hs5 | hs5
            · -- n < 201798561
              exact Brocard.berndt_galway_chunk_1122 n m (by omega) (by omega) h
            · -- n >= 201798561
              exact Brocard.berndt_galway_chunk_1123 n m (by omega) (by omega) h
          · -- n >= 201978417
            exact Brocard.berndt_galway_chunk_1124 n m (by omega) (by omega) h
    · -- n >= 202158273
      rcases Nat.lt_or_ge n 203237410 with hs2 | hs2
      · -- n < 203237410
        rcases Nat.lt_or_ge n 202697841 with hs3 | hs3
        · -- n < 202697841
          rcases Nat.lt_or_ge n 202517985 with hs4 | hs4
          · -- n < 202517985
            rcases Nat.lt_or_ge n 202338129 with hs5 | hs5
            · -- n < 202338129
              exact Brocard.berndt_galway_chunk_1125 n m (by omega) (by omega) h
            · -- n >= 202338129
              exact Brocard.berndt_galway_chunk_1126 n m (by omega) (by omega) h
          · -- n >= 202517985
            exact Brocard.berndt_galway_chunk_1127 n m (by omega) (by omega) h
        · -- n >= 202697841
          rcases Nat.lt_or_ge n 203057553 with hs4 | hs4
          · -- n < 203057553
            rcases Nat.lt_or_ge n 202877697 with hs5 | hs5
            · -- n < 202877697
              exact Brocard.berndt_galway_chunk_1128 n m (by omega) (by omega) h
            · -- n >= 202877697
              exact Brocard.berndt_galway_chunk_1129 n m (by omega) (by omega) h
          · -- n >= 203057553
            exact Brocard.berndt_galway_chunk_1130 n m (by omega) (by omega) h
      · -- n >= 203237410
        rcases Nat.lt_or_ge n 203776978 with hs3 | hs3
        · -- n < 203776978
          rcases Nat.lt_or_ge n 203597122 with hs4 | hs4
          · -- n < 203597122
            rcases Nat.lt_or_ge n 203417266 with hs5 | hs5
            · -- n < 203417266
              exact Brocard.berndt_galway_chunk_1131 n m (by omega) (by omega) h
            · -- n >= 203417266
              exact Brocard.berndt_galway_chunk_1132 n m (by omega) (by omega) h
          · -- n >= 203597122
            exact Brocard.berndt_galway_chunk_1133 n m (by omega) (by omega) h
        · -- n >= 203776978
          rcases Nat.lt_or_ge n 204136690 with hs4 | hs4
          · -- n < 204136690
            rcases Nat.lt_or_ge n 203956834 with hs5 | hs5
            · -- n < 203956834
              exact Brocard.berndt_galway_chunk_1134 n m (by omega) (by omega) h
            · -- n >= 203956834
              exact Brocard.berndt_galway_chunk_1135 n m (by omega) (by omega) h
          · -- n >= 204136690
            exact Brocard.berndt_galway_chunk_1136 n m (by omega) (by omega) h
  · -- n >= 204316546
    rcases Nat.lt_or_ge n 206474820 with hs1 | hs1
    · -- n < 206474820
      rcases Nat.lt_or_ge n 205395683 with hs2 | hs2
      · -- n < 205395683
        rcases Nat.lt_or_ge n 204856115 with hs3 | hs3
        · -- n < 204856115
          rcases Nat.lt_or_ge n 204676258 with hs4 | hs4
          · -- n < 204676258
            rcases Nat.lt_or_ge n 204496402 with hs5 | hs5
            · -- n < 204496402
              exact Brocard.berndt_galway_chunk_1137 n m (by omega) (by omega) h
            · -- n >= 204496402
              exact Brocard.berndt_galway_chunk_1138 n m (by omega) (by omega) h
          · -- n >= 204676258
            exact Brocard.berndt_galway_chunk_1139 n m (by omega) (by omega) h
        · -- n >= 204856115
          rcases Nat.lt_or_ge n 205215827 with hs4 | hs4
          · -- n < 205215827
            rcases Nat.lt_or_ge n 205035971 with hs5 | hs5
            · -- n < 205035971
              exact Brocard.berndt_galway_chunk_1140 n m (by omega) (by omega) h
            · -- n >= 205035971
              exact Brocard.berndt_galway_chunk_1141 n m (by omega) (by omega) h
          · -- n >= 205215827
            exact Brocard.berndt_galway_chunk_1142 n m (by omega) (by omega) h
      · -- n >= 205395683
        rcases Nat.lt_or_ge n 205935251 with hs3 | hs3
        · -- n < 205935251
          rcases Nat.lt_or_ge n 205755395 with hs4 | hs4
          · -- n < 205755395
            rcases Nat.lt_or_ge n 205575539 with hs5 | hs5
            · -- n < 205575539
              exact Brocard.berndt_galway_chunk_1143 n m (by omega) (by omega) h
            · -- n >= 205575539
              exact Brocard.berndt_galway_chunk_1144 n m (by omega) (by omega) h
          · -- n >= 205755395
            exact Brocard.berndt_galway_chunk_1145 n m (by omega) (by omega) h
        · -- n >= 205935251
          rcases Nat.lt_or_ge n 206294964 with hs4 | hs4
          · -- n < 206294964
            rcases Nat.lt_or_ge n 206115107 with hs5 | hs5
            · -- n < 206115107
              exact Brocard.berndt_galway_chunk_1146 n m (by omega) (by omega) h
            · -- n >= 206115107
              exact Brocard.berndt_galway_chunk_1147 n m (by omega) (by omega) h
          · -- n >= 206294964
            exact Brocard.berndt_galway_chunk_1148 n m (by omega) (by omega) h
    · -- n >= 206474820
      rcases Nat.lt_or_ge n 207553956 with hs2 | hs2
      · -- n < 207553956
        rcases Nat.lt_or_ge n 207014388 with hs3 | hs3
        · -- n < 207014388
          rcases Nat.lt_or_ge n 206834532 with hs4 | hs4
          · -- n < 206834532
            rcases Nat.lt_or_ge n 206654676 with hs5 | hs5
            · -- n < 206654676
              exact Brocard.berndt_galway_chunk_1149 n m (by omega) (by omega) h
            · -- n >= 206654676
              exact Brocard.berndt_galway_chunk_1150 n m (by omega) (by omega) h
          · -- n >= 206834532
            exact Brocard.berndt_galway_chunk_1151 n m (by omega) (by omega) h
        · -- n >= 207014388
          rcases Nat.lt_or_ge n 207374100 with hs4 | hs4
          · -- n < 207374100
            rcases Nat.lt_or_ge n 207194244 with hs5 | hs5
            · -- n < 207194244
              exact Brocard.berndt_galway_chunk_1152 n m (by omega) (by omega) h
            · -- n >= 207194244
              exact Brocard.berndt_galway_chunk_1153 n m (by omega) (by omega) h
          · -- n >= 207374100
            exact Brocard.berndt_galway_chunk_1154 n m (by omega) (by omega) h
      · -- n >= 207553956
        rcases Nat.lt_or_ge n 208093525 with hs3 | hs3
        · -- n < 208093525
          rcases Nat.lt_or_ge n 207913669 with hs4 | hs4
          · -- n < 207913669
            rcases Nat.lt_or_ge n 207733812 with hs5 | hs5
            · -- n < 207733812
              exact Brocard.berndt_galway_chunk_1155 n m (by omega) (by omega) h
            · -- n >= 207733812
              exact Brocard.berndt_galway_chunk_1156 n m (by omega) (by omega) h
          · -- n >= 207913669
            exact Brocard.berndt_galway_chunk_1157 n m (by omega) (by omega) h
        · -- n >= 208093525
          rcases Nat.lt_or_ge n 208273381 with hs4 | hs4
          · -- n < 208273381
            exact Brocard.berndt_galway_chunk_1158 n m (by omega) (by omega) h
          · -- n >= 208273381
            exact Brocard.berndt_galway_chunk_1159 n m (by omega) (by omega) h
