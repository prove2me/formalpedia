-- Prove2me | solution 1 for Brocard.berndt_galway_group_026
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:52:45.069015+00:00
-- url     : https://prove2.me/submissions/f912c900-95f1-4322-b1bb-2da088f474a4

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_1160
import Theorems.Thm_Brocard_berndt_galway_chunk_1161
import Theorems.Thm_Brocard_berndt_galway_chunk_1162
import Theorems.Thm_Brocard_berndt_galway_chunk_1163
import Theorems.Thm_Brocard_berndt_galway_chunk_1164
import Theorems.Thm_Brocard_berndt_galway_chunk_1165
import Theorems.Thm_Brocard_berndt_galway_chunk_1166
import Theorems.Thm_Brocard_berndt_galway_chunk_1167
import Theorems.Thm_Brocard_berndt_galway_chunk_1168
import Theorems.Thm_Brocard_berndt_galway_chunk_1169
import Theorems.Thm_Brocard_berndt_galway_chunk_1170
import Theorems.Thm_Brocard_berndt_galway_chunk_1171
import Theorems.Thm_Brocard_berndt_galway_chunk_1172
import Theorems.Thm_Brocard_berndt_galway_chunk_1173
import Theorems.Thm_Brocard_berndt_galway_chunk_1174
import Theorems.Thm_Brocard_berndt_galway_chunk_1175
import Theorems.Thm_Brocard_berndt_galway_chunk_1176
import Theorems.Thm_Brocard_berndt_galway_chunk_1177
import Theorems.Thm_Brocard_berndt_galway_chunk_1178
import Theorems.Thm_Brocard_berndt_galway_chunk_1179
import Theorems.Thm_Brocard_berndt_galway_chunk_1180
import Theorems.Thm_Brocard_berndt_galway_chunk_1181
import Theorems.Thm_Brocard_berndt_galway_chunk_1182
import Theorems.Thm_Brocard_berndt_galway_chunk_1183
import Theorems.Thm_Brocard_berndt_galway_chunk_1184
import Theorems.Thm_Brocard_berndt_galway_chunk_1185
import Theorems.Thm_Brocard_berndt_galway_chunk_1186
import Theorems.Thm_Brocard_berndt_galway_chunk_1187
import Theorems.Thm_Brocard_berndt_galway_chunk_1188
import Theorems.Thm_Brocard_berndt_galway_chunk_1189
import Theorems.Thm_Brocard_berndt_galway_chunk_1190
import Theorems.Thm_Brocard_berndt_galway_chunk_1191
import Theorems.Thm_Brocard_berndt_galway_chunk_1192
import Theorems.Thm_Brocard_berndt_galway_chunk_1193
import Theorems.Thm_Brocard_berndt_galway_chunk_1194
import Theorems.Thm_Brocard_berndt_galway_chunk_1195
import Theorems.Thm_Brocard_berndt_galway_chunk_1196
import Theorems.Thm_Brocard_berndt_galway_chunk_1197
import Theorems.Thm_Brocard_berndt_galway_chunk_1198
import Theorems.Thm_Brocard_berndt_galway_chunk_1199
import Theorems.Thm_Brocard_berndt_galway_chunk_1200
import Theorems.Thm_Brocard_berndt_galway_chunk_1201
import Theorems.Thm_Brocard_berndt_galway_chunk_1202
import Theorems.Thm_Brocard_berndt_galway_chunk_1203
import Theorems.Thm_Brocard_berndt_galway_chunk_1204
import Theorems.Thm_Brocard_berndt_galway_chunk_1205
import Theorems.Thm_Brocard_berndt_galway_chunk_1206

theorem solution (n m : ℕ) (h1 : 208453237 ≤ n) (h2 : n < 216906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 212769784 with hs0 | hs0
  · -- n < 212769784
    rcases Nat.lt_or_ge n 210611510 with hs1 | hs1
    · -- n < 210611510
      rcases Nat.lt_or_ge n 209532374 with hs2 | hs2
      · -- n < 209532374
        rcases Nat.lt_or_ge n 208992805 with hs3 | hs3
        · -- n < 208992805
          rcases Nat.lt_or_ge n 208812949 with hs4 | hs4
          · -- n < 208812949
            rcases Nat.lt_or_ge n 208633093 with hs5 | hs5
            · -- n < 208633093
              exact Brocard.berndt_galway_chunk_1160 n m (by omega) (by omega) h
            · -- n >= 208633093
              exact Brocard.berndt_galway_chunk_1161 n m (by omega) (by omega) h
          · -- n >= 208812949
            exact Brocard.berndt_galway_chunk_1162 n m (by omega) (by omega) h
        · -- n >= 208992805
          rcases Nat.lt_or_ge n 209352517 with hs4 | hs4
          · -- n < 209352517
            rcases Nat.lt_or_ge n 209172661 with hs5 | hs5
            · -- n < 209172661
              exact Brocard.berndt_galway_chunk_1163 n m (by omega) (by omega) h
            · -- n >= 209172661
              exact Brocard.berndt_galway_chunk_1164 n m (by omega) (by omega) h
          · -- n >= 209352517
            exact Brocard.berndt_galway_chunk_1165 n m (by omega) (by omega) h
      · -- n >= 209532374
        rcases Nat.lt_or_ge n 210071942 with hs3 | hs3
        · -- n < 210071942
          rcases Nat.lt_or_ge n 209892086 with hs4 | hs4
          · -- n < 209892086
            rcases Nat.lt_or_ge n 209712230 with hs5 | hs5
            · -- n < 209712230
              exact Brocard.berndt_galway_chunk_1166 n m (by omega) (by omega) h
            · -- n >= 209712230
              exact Brocard.berndt_galway_chunk_1167 n m (by omega) (by omega) h
          · -- n >= 209892086
            exact Brocard.berndt_galway_chunk_1168 n m (by omega) (by omega) h
        · -- n >= 210071942
          rcases Nat.lt_or_ge n 210431654 with hs4 | hs4
          · -- n < 210431654
            rcases Nat.lt_or_ge n 210251798 with hs5 | hs5
            · -- n < 210251798
              exact Brocard.berndt_galway_chunk_1169 n m (by omega) (by omega) h
            · -- n >= 210251798
              exact Brocard.berndt_galway_chunk_1170 n m (by omega) (by omega) h
          · -- n >= 210431654
            exact Brocard.berndt_galway_chunk_1171 n m (by omega) (by omega) h
    · -- n >= 210611510
      rcases Nat.lt_or_ge n 211690647 with hs2 | hs2
      · -- n < 211690647
        rcases Nat.lt_or_ge n 211151079 with hs3 | hs3
        · -- n < 211151079
          rcases Nat.lt_or_ge n 210971223 with hs4 | hs4
          · -- n < 210971223
            rcases Nat.lt_or_ge n 210791366 with hs5 | hs5
            · -- n < 210791366
              exact Brocard.berndt_galway_chunk_1172 n m (by omega) (by omega) h
            · -- n >= 210791366
              exact Brocard.berndt_galway_chunk_1173 n m (by omega) (by omega) h
          · -- n >= 210971223
            exact Brocard.berndt_galway_chunk_1174 n m (by omega) (by omega) h
        · -- n >= 211151079
          rcases Nat.lt_or_ge n 211510791 with hs4 | hs4
          · -- n < 211510791
            rcases Nat.lt_or_ge n 211330935 with hs5 | hs5
            · -- n < 211330935
              exact Brocard.berndt_galway_chunk_1175 n m (by omega) (by omega) h
            · -- n >= 211330935
              exact Brocard.berndt_galway_chunk_1176 n m (by omega) (by omega) h
          · -- n >= 211510791
            exact Brocard.berndt_galway_chunk_1177 n m (by omega) (by omega) h
      · -- n >= 211690647
        rcases Nat.lt_or_ge n 212230215 with hs3 | hs3
        · -- n < 212230215
          rcases Nat.lt_or_ge n 212050359 with hs4 | hs4
          · -- n < 212050359
            rcases Nat.lt_or_ge n 211870503 with hs5 | hs5
            · -- n < 211870503
              exact Brocard.berndt_galway_chunk_1178 n m (by omega) (by omega) h
            · -- n >= 211870503
              exact Brocard.berndt_galway_chunk_1179 n m (by omega) (by omega) h
          · -- n >= 212050359
            exact Brocard.berndt_galway_chunk_1180 n m (by omega) (by omega) h
        · -- n >= 212230215
          rcases Nat.lt_or_ge n 212589928 with hs4 | hs4
          · -- n < 212589928
            rcases Nat.lt_or_ge n 212410071 with hs5 | hs5
            · -- n < 212410071
              exact Brocard.berndt_galway_chunk_1181 n m (by omega) (by omega) h
            · -- n >= 212410071
              exact Brocard.berndt_galway_chunk_1182 n m (by omega) (by omega) h
          · -- n >= 212589928
            exact Brocard.berndt_galway_chunk_1183 n m (by omega) (by omega) h
  · -- n >= 212769784
    rcases Nat.lt_or_ge n 214928057 with hs1 | hs1
    · -- n < 214928057
      rcases Nat.lt_or_ge n 213848920 with hs2 | hs2
      · -- n < 213848920
        rcases Nat.lt_or_ge n 213309352 with hs3 | hs3
        · -- n < 213309352
          rcases Nat.lt_or_ge n 213129496 with hs4 | hs4
          · -- n < 213129496
            rcases Nat.lt_or_ge n 212949640 with hs5 | hs5
            · -- n < 212949640
              exact Brocard.berndt_galway_chunk_1184 n m (by omega) (by omega) h
            · -- n >= 212949640
              exact Brocard.berndt_galway_chunk_1185 n m (by omega) (by omega) h
          · -- n >= 213129496
            exact Brocard.berndt_galway_chunk_1186 n m (by omega) (by omega) h
        · -- n >= 213309352
          rcases Nat.lt_or_ge n 213669064 with hs4 | hs4
          · -- n < 213669064
            rcases Nat.lt_or_ge n 213489208 with hs5 | hs5
            · -- n < 213489208
              exact Brocard.berndt_galway_chunk_1187 n m (by omega) (by omega) h
            · -- n >= 213489208
              exact Brocard.berndt_galway_chunk_1188 n m (by omega) (by omega) h
          · -- n >= 213669064
            exact Brocard.berndt_galway_chunk_1189 n m (by omega) (by omega) h
      · -- n >= 213848920
        rcases Nat.lt_or_ge n 214388489 with hs3 | hs3
        · -- n < 214388489
          rcases Nat.lt_or_ge n 214208633 with hs4 | hs4
          · -- n < 214208633
            rcases Nat.lt_or_ge n 214028776 with hs5 | hs5
            · -- n < 214028776
              exact Brocard.berndt_galway_chunk_1190 n m (by omega) (by omega) h
            · -- n >= 214028776
              exact Brocard.berndt_galway_chunk_1191 n m (by omega) (by omega) h
          · -- n >= 214208633
            exact Brocard.berndt_galway_chunk_1192 n m (by omega) (by omega) h
        · -- n >= 214388489
          rcases Nat.lt_or_ge n 214748201 with hs4 | hs4
          · -- n < 214748201
            rcases Nat.lt_or_ge n 214568345 with hs5 | hs5
            · -- n < 214568345
              exact Brocard.berndt_galway_chunk_1193 n m (by omega) (by omega) h
            · -- n >= 214568345
              exact Brocard.berndt_galway_chunk_1194 n m (by omega) (by omega) h
          · -- n >= 214748201
            exact Brocard.berndt_galway_chunk_1195 n m (by omega) (by omega) h
    · -- n >= 214928057
      rcases Nat.lt_or_ge n 216007194 with hs2 | hs2
      · -- n < 216007194
        rcases Nat.lt_or_ge n 215467625 with hs3 | hs3
        · -- n < 215467625
          rcases Nat.lt_or_ge n 215287769 with hs4 | hs4
          · -- n < 215287769
            rcases Nat.lt_or_ge n 215107913 with hs5 | hs5
            · -- n < 215107913
              exact Brocard.berndt_galway_chunk_1196 n m (by omega) (by omega) h
            · -- n >= 215107913
              exact Brocard.berndt_galway_chunk_1197 n m (by omega) (by omega) h
          · -- n >= 215287769
            exact Brocard.berndt_galway_chunk_1198 n m (by omega) (by omega) h
        · -- n >= 215467625
          rcases Nat.lt_or_ge n 215827338 with hs4 | hs4
          · -- n < 215827338
            rcases Nat.lt_or_ge n 215647482 with hs5 | hs5
            · -- n < 215647482
              exact Brocard.berndt_galway_chunk_1199 n m (by omega) (by omega) h
            · -- n >= 215647482
              exact Brocard.berndt_galway_chunk_1200 n m (by omega) (by omega) h
          · -- n >= 215827338
            exact Brocard.berndt_galway_chunk_1201 n m (by omega) (by omega) h
      · -- n >= 216007194
        rcases Nat.lt_or_ge n 216546762 with hs3 | hs3
        · -- n < 216546762
          rcases Nat.lt_or_ge n 216366906 with hs4 | hs4
          · -- n < 216366906
            rcases Nat.lt_or_ge n 216187050 with hs5 | hs5
            · -- n < 216187050
              exact Brocard.berndt_galway_chunk_1202 n m (by omega) (by omega) h
            · -- n >= 216187050
              exact Brocard.berndt_galway_chunk_1203 n m (by omega) (by omega) h
          · -- n >= 216366906
            exact Brocard.berndt_galway_chunk_1204 n m (by omega) (by omega) h
        · -- n >= 216546762
          rcases Nat.lt_or_ge n 216726618 with hs4 | hs4
          · -- n < 216726618
            exact Brocard.berndt_galway_chunk_1205 n m (by omega) (by omega) h
          · -- n >= 216726618
            exact Brocard.berndt_galway_chunk_1206 n m (by omega) (by omega) h
