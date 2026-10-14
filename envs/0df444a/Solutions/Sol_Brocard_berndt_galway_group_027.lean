-- Prove2me | solution 1 for Brocard.berndt_galway_group_027
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:07:38.541472+00:00
-- url     : https://prove2.me/submissions/414658d4-2b99-479c-a6f2-c4b519cccbf5

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_1207
import Theorems.Thm_Brocard_berndt_galway_chunk_1208
import Theorems.Thm_Brocard_berndt_galway_chunk_1209
import Theorems.Thm_Brocard_berndt_galway_chunk_1210
import Theorems.Thm_Brocard_berndt_galway_chunk_1211
import Theorems.Thm_Brocard_berndt_galway_chunk_1212
import Theorems.Thm_Brocard_berndt_galway_chunk_1213
import Theorems.Thm_Brocard_berndt_galway_chunk_1214
import Theorems.Thm_Brocard_berndt_galway_chunk_1215
import Theorems.Thm_Brocard_berndt_galway_chunk_1216
import Theorems.Thm_Brocard_berndt_galway_chunk_1217
import Theorems.Thm_Brocard_berndt_galway_chunk_1218
import Theorems.Thm_Brocard_berndt_galway_chunk_1219
import Theorems.Thm_Brocard_berndt_galway_chunk_1220
import Theorems.Thm_Brocard_berndt_galway_chunk_1221
import Theorems.Thm_Brocard_berndt_galway_chunk_1222
import Theorems.Thm_Brocard_berndt_galway_chunk_1223
import Theorems.Thm_Brocard_berndt_galway_chunk_1224
import Theorems.Thm_Brocard_berndt_galway_chunk_1225
import Theorems.Thm_Brocard_berndt_galway_chunk_1226
import Theorems.Thm_Brocard_berndt_galway_chunk_1227
import Theorems.Thm_Brocard_berndt_galway_chunk_1228
import Theorems.Thm_Brocard_berndt_galway_chunk_1229
import Theorems.Thm_Brocard_berndt_galway_chunk_1230
import Theorems.Thm_Brocard_berndt_galway_chunk_1231
import Theorems.Thm_Brocard_berndt_galway_chunk_1232
import Theorems.Thm_Brocard_berndt_galway_chunk_1233
import Theorems.Thm_Brocard_berndt_galway_chunk_1234
import Theorems.Thm_Brocard_berndt_galway_chunk_1235
import Theorems.Thm_Brocard_berndt_galway_chunk_1236
import Theorems.Thm_Brocard_berndt_galway_chunk_1237
import Theorems.Thm_Brocard_berndt_galway_chunk_1238
import Theorems.Thm_Brocard_berndt_galway_chunk_1239
import Theorems.Thm_Brocard_berndt_galway_chunk_1240
import Theorems.Thm_Brocard_berndt_galway_chunk_1241
import Theorems.Thm_Brocard_berndt_galway_chunk_1242
import Theorems.Thm_Brocard_berndt_galway_chunk_1243
import Theorems.Thm_Brocard_berndt_galway_chunk_1244
import Theorems.Thm_Brocard_berndt_galway_chunk_1245
import Theorems.Thm_Brocard_berndt_galway_chunk_1246
import Theorems.Thm_Brocard_berndt_galway_chunk_1247
import Theorems.Thm_Brocard_berndt_galway_chunk_1248
import Theorems.Thm_Brocard_berndt_galway_chunk_1249
import Theorems.Thm_Brocard_berndt_galway_chunk_1250
import Theorems.Thm_Brocard_berndt_galway_chunk_1251
import Theorems.Thm_Brocard_berndt_galway_chunk_1252
import Theorems.Thm_Brocard_berndt_galway_chunk_1253

theorem solution (n m : ℕ) (h1 : 216906474 ≤ n) (h2 : n < 225359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 221223021 with hs0 | hs0
  · -- n < 221223021
    rcases Nat.lt_or_ge n 219064748 with hs1 | hs1
    · -- n < 219064748
      rcases Nat.lt_or_ge n 217985611 with hs2 | hs2
      · -- n < 217985611
        rcases Nat.lt_or_ge n 217446043 with hs3 | hs3
        · -- n < 217446043
          rcases Nat.lt_or_ge n 217266187 with hs4 | hs4
          · -- n < 217266187
            rcases Nat.lt_or_ge n 217086330 with hs5 | hs5
            · -- n < 217086330
              exact Brocard.berndt_galway_chunk_1207 n m (by omega) (by omega) h
            · -- n >= 217086330
              exact Brocard.berndt_galway_chunk_1208 n m (by omega) (by omega) h
          · -- n >= 217266187
            exact Brocard.berndt_galway_chunk_1209 n m (by omega) (by omega) h
        · -- n >= 217446043
          rcases Nat.lt_or_ge n 217805755 with hs4 | hs4
          · -- n < 217805755
            rcases Nat.lt_or_ge n 217625899 with hs5 | hs5
            · -- n < 217625899
              exact Brocard.berndt_galway_chunk_1210 n m (by omega) (by omega) h
            · -- n >= 217625899
              exact Brocard.berndt_galway_chunk_1211 n m (by omega) (by omega) h
          · -- n >= 217805755
            exact Brocard.berndt_galway_chunk_1212 n m (by omega) (by omega) h
      · -- n >= 217985611
        rcases Nat.lt_or_ge n 218525179 with hs3 | hs3
        · -- n < 218525179
          rcases Nat.lt_or_ge n 218345323 with hs4 | hs4
          · -- n < 218345323
            rcases Nat.lt_or_ge n 218165467 with hs5 | hs5
            · -- n < 218165467
              exact Brocard.berndt_galway_chunk_1213 n m (by omega) (by omega) h
            · -- n >= 218165467
              exact Brocard.berndt_galway_chunk_1214 n m (by omega) (by omega) h
          · -- n >= 218345323
            exact Brocard.berndt_galway_chunk_1215 n m (by omega) (by omega) h
        · -- n >= 218525179
          rcases Nat.lt_or_ge n 218884892 with hs4 | hs4
          · -- n < 218884892
            rcases Nat.lt_or_ge n 218705035 with hs5 | hs5
            · -- n < 218705035
              exact Brocard.berndt_galway_chunk_1216 n m (by omega) (by omega) h
            · -- n >= 218705035
              exact Brocard.berndt_galway_chunk_1217 n m (by omega) (by omega) h
          · -- n >= 218884892
            exact Brocard.berndt_galway_chunk_1218 n m (by omega) (by omega) h
    · -- n >= 219064748
      rcases Nat.lt_or_ge n 220143884 with hs2 | hs2
      · -- n < 220143884
        rcases Nat.lt_or_ge n 219604316 with hs3 | hs3
        · -- n < 219604316
          rcases Nat.lt_or_ge n 219424460 with hs4 | hs4
          · -- n < 219424460
            rcases Nat.lt_or_ge n 219244604 with hs5 | hs5
            · -- n < 219244604
              exact Brocard.berndt_galway_chunk_1219 n m (by omega) (by omega) h
            · -- n >= 219244604
              exact Brocard.berndt_galway_chunk_1220 n m (by omega) (by omega) h
          · -- n >= 219424460
            exact Brocard.berndt_galway_chunk_1221 n m (by omega) (by omega) h
        · -- n >= 219604316
          rcases Nat.lt_or_ge n 219964028 with hs4 | hs4
          · -- n < 219964028
            rcases Nat.lt_or_ge n 219784172 with hs5 | hs5
            · -- n < 219784172
              exact Brocard.berndt_galway_chunk_1222 n m (by omega) (by omega) h
            · -- n >= 219784172
              exact Brocard.berndt_galway_chunk_1223 n m (by omega) (by omega) h
          · -- n >= 219964028
            exact Brocard.berndt_galway_chunk_1224 n m (by omega) (by omega) h
      · -- n >= 220143884
        rcases Nat.lt_or_ge n 220683453 with hs3 | hs3
        · -- n < 220683453
          rcases Nat.lt_or_ge n 220503597 with hs4 | hs4
          · -- n < 220503597
            rcases Nat.lt_or_ge n 220323741 with hs5 | hs5
            · -- n < 220323741
              exact Brocard.berndt_galway_chunk_1225 n m (by omega) (by omega) h
            · -- n >= 220323741
              exact Brocard.berndt_galway_chunk_1226 n m (by omega) (by omega) h
          · -- n >= 220503597
            exact Brocard.berndt_galway_chunk_1227 n m (by omega) (by omega) h
        · -- n >= 220683453
          rcases Nat.lt_or_ge n 221043165 with hs4 | hs4
          · -- n < 221043165
            rcases Nat.lt_or_ge n 220863309 with hs5 | hs5
            · -- n < 220863309
              exact Brocard.berndt_galway_chunk_1228 n m (by omega) (by omega) h
            · -- n >= 220863309
              exact Brocard.berndt_galway_chunk_1229 n m (by omega) (by omega) h
          · -- n >= 221043165
            exact Brocard.berndt_galway_chunk_1230 n m (by omega) (by omega) h
  · -- n >= 221223021
    rcases Nat.lt_or_ge n 223381294 with hs1 | hs1
    · -- n < 223381294
      rcases Nat.lt_or_ge n 222302158 with hs2 | hs2
      · -- n < 222302158
        rcases Nat.lt_or_ge n 221762589 with hs3 | hs3
        · -- n < 221762589
          rcases Nat.lt_or_ge n 221582733 with hs4 | hs4
          · -- n < 221582733
            rcases Nat.lt_or_ge n 221402877 with hs5 | hs5
            · -- n < 221402877
              exact Brocard.berndt_galway_chunk_1231 n m (by omega) (by omega) h
            · -- n >= 221402877
              exact Brocard.berndt_galway_chunk_1232 n m (by omega) (by omega) h
          · -- n >= 221582733
            exact Brocard.berndt_galway_chunk_1233 n m (by omega) (by omega) h
        · -- n >= 221762589
          rcases Nat.lt_or_ge n 222122302 with hs4 | hs4
          · -- n < 222122302
            rcases Nat.lt_or_ge n 221942446 with hs5 | hs5
            · -- n < 221942446
              exact Brocard.berndt_galway_chunk_1234 n m (by omega) (by omega) h
            · -- n >= 221942446
              exact Brocard.berndt_galway_chunk_1235 n m (by omega) (by omega) h
          · -- n >= 222122302
            exact Brocard.berndt_galway_chunk_1236 n m (by omega) (by omega) h
      · -- n >= 222302158
        rcases Nat.lt_or_ge n 222841726 with hs3 | hs3
        · -- n < 222841726
          rcases Nat.lt_or_ge n 222661870 with hs4 | hs4
          · -- n < 222661870
            rcases Nat.lt_or_ge n 222482014 with hs5 | hs5
            · -- n < 222482014
              exact Brocard.berndt_galway_chunk_1237 n m (by omega) (by omega) h
            · -- n >= 222482014
              exact Brocard.berndt_galway_chunk_1238 n m (by omega) (by omega) h
          · -- n >= 222661870
            exact Brocard.berndt_galway_chunk_1239 n m (by omega) (by omega) h
        · -- n >= 222841726
          rcases Nat.lt_or_ge n 223201438 with hs4 | hs4
          · -- n < 223201438
            rcases Nat.lt_or_ge n 223021582 with hs5 | hs5
            · -- n < 223021582
              exact Brocard.berndt_galway_chunk_1240 n m (by omega) (by omega) h
            · -- n >= 223021582
              exact Brocard.berndt_galway_chunk_1241 n m (by omega) (by omega) h
          · -- n >= 223201438
            exact Brocard.berndt_galway_chunk_1242 n m (by omega) (by omega) h
    · -- n >= 223381294
      rcases Nat.lt_or_ge n 224460431 with hs2 | hs2
      · -- n < 224460431
        rcases Nat.lt_or_ge n 223920863 with hs3 | hs3
        · -- n < 223920863
          rcases Nat.lt_or_ge n 223741007 with hs4 | hs4
          · -- n < 223741007
            rcases Nat.lt_or_ge n 223561151 with hs5 | hs5
            · -- n < 223561151
              exact Brocard.berndt_galway_chunk_1243 n m (by omega) (by omega) h
            · -- n >= 223561151
              exact Brocard.berndt_galway_chunk_1244 n m (by omega) (by omega) h
          · -- n >= 223741007
            exact Brocard.berndt_galway_chunk_1245 n m (by omega) (by omega) h
        · -- n >= 223920863
          rcases Nat.lt_or_ge n 224280575 with hs4 | hs4
          · -- n < 224280575
            rcases Nat.lt_or_ge n 224100719 with hs5 | hs5
            · -- n < 224100719
              exact Brocard.berndt_galway_chunk_1246 n m (by omega) (by omega) h
            · -- n >= 224100719
              exact Brocard.berndt_galway_chunk_1247 n m (by omega) (by omega) h
          · -- n >= 224280575
            exact Brocard.berndt_galway_chunk_1248 n m (by omega) (by omega) h
      · -- n >= 224460431
        rcases Nat.lt_or_ge n 225000000 with hs3 | hs3
        · -- n < 225000000
          rcases Nat.lt_or_ge n 224820143 with hs4 | hs4
          · -- n < 224820143
            rcases Nat.lt_or_ge n 224640287 with hs5 | hs5
            · -- n < 224640287
              exact Brocard.berndt_galway_chunk_1249 n m (by omega) (by omega) h
            · -- n >= 224640287
              exact Brocard.berndt_galway_chunk_1250 n m (by omega) (by omega) h
          · -- n >= 224820143
            exact Brocard.berndt_galway_chunk_1251 n m (by omega) (by omega) h
        · -- n >= 225000000
          rcases Nat.lt_or_ge n 225179856 with hs4 | hs4
          · -- n < 225179856
            exact Brocard.berndt_galway_chunk_1252 n m (by omega) (by omega) h
          · -- n >= 225179856
            exact Brocard.berndt_galway_chunk_1253 n m (by omega) (by omega) h
