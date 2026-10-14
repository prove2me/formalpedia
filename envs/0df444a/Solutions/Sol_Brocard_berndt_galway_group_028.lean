-- Prove2me | solution 1 for Brocard.berndt_galway_group_028
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:22:24.138595+00:00
-- url     : https://prove2.me/submissions/57e956ea-09a8-4933-b021-5febfdd9274c

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_1254
import Theorems.Thm_Brocard_berndt_galway_chunk_1255
import Theorems.Thm_Brocard_berndt_galway_chunk_1256
import Theorems.Thm_Brocard_berndt_galway_chunk_1257
import Theorems.Thm_Brocard_berndt_galway_chunk_1258
import Theorems.Thm_Brocard_berndt_galway_chunk_1259
import Theorems.Thm_Brocard_berndt_galway_chunk_1260
import Theorems.Thm_Brocard_berndt_galway_chunk_1261
import Theorems.Thm_Brocard_berndt_galway_chunk_1262
import Theorems.Thm_Brocard_berndt_galway_chunk_1263
import Theorems.Thm_Brocard_berndt_galway_chunk_1264
import Theorems.Thm_Brocard_berndt_galway_chunk_1265
import Theorems.Thm_Brocard_berndt_galway_chunk_1266
import Theorems.Thm_Brocard_berndt_galway_chunk_1267
import Theorems.Thm_Brocard_berndt_galway_chunk_1268
import Theorems.Thm_Brocard_berndt_galway_chunk_1269
import Theorems.Thm_Brocard_berndt_galway_chunk_1270
import Theorems.Thm_Brocard_berndt_galway_chunk_1271
import Theorems.Thm_Brocard_berndt_galway_chunk_1272
import Theorems.Thm_Brocard_berndt_galway_chunk_1273
import Theorems.Thm_Brocard_berndt_galway_chunk_1274
import Theorems.Thm_Brocard_berndt_galway_chunk_1275
import Theorems.Thm_Brocard_berndt_galway_chunk_1276
import Theorems.Thm_Brocard_berndt_galway_chunk_1277
import Theorems.Thm_Brocard_berndt_galway_chunk_1278
import Theorems.Thm_Brocard_berndt_galway_chunk_1279
import Theorems.Thm_Brocard_berndt_galway_chunk_1280
import Theorems.Thm_Brocard_berndt_galway_chunk_1281
import Theorems.Thm_Brocard_berndt_galway_chunk_1282
import Theorems.Thm_Brocard_berndt_galway_chunk_1283
import Theorems.Thm_Brocard_berndt_galway_chunk_1284
import Theorems.Thm_Brocard_berndt_galway_chunk_1285
import Theorems.Thm_Brocard_berndt_galway_chunk_1286
import Theorems.Thm_Brocard_berndt_galway_chunk_1287
import Theorems.Thm_Brocard_berndt_galway_chunk_1288
import Theorems.Thm_Brocard_berndt_galway_chunk_1289
import Theorems.Thm_Brocard_berndt_galway_chunk_1290
import Theorems.Thm_Brocard_berndt_galway_chunk_1291
import Theorems.Thm_Brocard_berndt_galway_chunk_1292
import Theorems.Thm_Brocard_berndt_galway_chunk_1293
import Theorems.Thm_Brocard_berndt_galway_chunk_1294
import Theorems.Thm_Brocard_berndt_galway_chunk_1295
import Theorems.Thm_Brocard_berndt_galway_chunk_1296
import Theorems.Thm_Brocard_berndt_galway_chunk_1297
import Theorems.Thm_Brocard_berndt_galway_chunk_1298
import Theorems.Thm_Brocard_berndt_galway_chunk_1299
import Theorems.Thm_Brocard_berndt_galway_chunk_1300

theorem solution (n m : ℕ) (h1 : 225359712 ≤ n) (h2 : n < 233812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 229676258 with hs0 | hs0
  · -- n < 229676258
    rcases Nat.lt_or_ge n 227517985 with hs1 | hs1
    · -- n < 227517985
      rcases Nat.lt_or_ge n 226438848 with hs2 | hs2
      · -- n < 226438848
        rcases Nat.lt_or_ge n 225899280 with hs3 | hs3
        · -- n < 225899280
          rcases Nat.lt_or_ge n 225719424 with hs4 | hs4
          · -- n < 225719424
            rcases Nat.lt_or_ge n 225539568 with hs5 | hs5
            · -- n < 225539568
              exact Brocard.berndt_galway_chunk_1254 n m (by omega) (by omega) h
            · -- n >= 225539568
              exact Brocard.berndt_galway_chunk_1255 n m (by omega) (by omega) h
          · -- n >= 225719424
            exact Brocard.berndt_galway_chunk_1256 n m (by omega) (by omega) h
        · -- n >= 225899280
          rcases Nat.lt_or_ge n 226258992 with hs4 | hs4
          · -- n < 226258992
            rcases Nat.lt_or_ge n 226079136 with hs5 | hs5
            · -- n < 226079136
              exact Brocard.berndt_galway_chunk_1257 n m (by omega) (by omega) h
            · -- n >= 226079136
              exact Brocard.berndt_galway_chunk_1258 n m (by omega) (by omega) h
          · -- n >= 226258992
            exact Brocard.berndt_galway_chunk_1259 n m (by omega) (by omega) h
      · -- n >= 226438848
        rcases Nat.lt_or_ge n 226978417 with hs3 | hs3
        · -- n < 226978417
          rcases Nat.lt_or_ge n 226798561 with hs4 | hs4
          · -- n < 226798561
            rcases Nat.lt_or_ge n 226618705 with hs5 | hs5
            · -- n < 226618705
              exact Brocard.berndt_galway_chunk_1260 n m (by omega) (by omega) h
            · -- n >= 226618705
              exact Brocard.berndt_galway_chunk_1261 n m (by omega) (by omega) h
          · -- n >= 226798561
            exact Brocard.berndt_galway_chunk_1262 n m (by omega) (by omega) h
        · -- n >= 226978417
          rcases Nat.lt_or_ge n 227338129 with hs4 | hs4
          · -- n < 227338129
            rcases Nat.lt_or_ge n 227158273 with hs5 | hs5
            · -- n < 227158273
              exact Brocard.berndt_galway_chunk_1263 n m (by omega) (by omega) h
            · -- n >= 227158273
              exact Brocard.berndt_galway_chunk_1264 n m (by omega) (by omega) h
          · -- n >= 227338129
            exact Brocard.berndt_galway_chunk_1265 n m (by omega) (by omega) h
    · -- n >= 227517985
      rcases Nat.lt_or_ge n 228597122 with hs2 | hs2
      · -- n < 228597122
        rcases Nat.lt_or_ge n 228057553 with hs3 | hs3
        · -- n < 228057553
          rcases Nat.lt_or_ge n 227877697 with hs4 | hs4
          · -- n < 227877697
            rcases Nat.lt_or_ge n 227697841 with hs5 | hs5
            · -- n < 227697841
              exact Brocard.berndt_galway_chunk_1266 n m (by omega) (by omega) h
            · -- n >= 227697841
              exact Brocard.berndt_galway_chunk_1267 n m (by omega) (by omega) h
          · -- n >= 227877697
            exact Brocard.berndt_galway_chunk_1268 n m (by omega) (by omega) h
        · -- n >= 228057553
          rcases Nat.lt_or_ge n 228417266 with hs4 | hs4
          · -- n < 228417266
            rcases Nat.lt_or_ge n 228237410 with hs5 | hs5
            · -- n < 228237410
              exact Brocard.berndt_galway_chunk_1269 n m (by omega) (by omega) h
            · -- n >= 228237410
              exact Brocard.berndt_galway_chunk_1270 n m (by omega) (by omega) h
          · -- n >= 228417266
            exact Brocard.berndt_galway_chunk_1271 n m (by omega) (by omega) h
      · -- n >= 228597122
        rcases Nat.lt_or_ge n 229136690 with hs3 | hs3
        · -- n < 229136690
          rcases Nat.lt_or_ge n 228956834 with hs4 | hs4
          · -- n < 228956834
            rcases Nat.lt_or_ge n 228776978 with hs5 | hs5
            · -- n < 228776978
              exact Brocard.berndt_galway_chunk_1272 n m (by omega) (by omega) h
            · -- n >= 228776978
              exact Brocard.berndt_galway_chunk_1273 n m (by omega) (by omega) h
          · -- n >= 228956834
            exact Brocard.berndt_galway_chunk_1274 n m (by omega) (by omega) h
        · -- n >= 229136690
          rcases Nat.lt_or_ge n 229496402 with hs4 | hs4
          · -- n < 229496402
            rcases Nat.lt_or_ge n 229316546 with hs5 | hs5
            · -- n < 229316546
              exact Brocard.berndt_galway_chunk_1275 n m (by omega) (by omega) h
            · -- n >= 229316546
              exact Brocard.berndt_galway_chunk_1276 n m (by omega) (by omega) h
          · -- n >= 229496402
            exact Brocard.berndt_galway_chunk_1277 n m (by omega) (by omega) h
  · -- n >= 229676258
    rcases Nat.lt_or_ge n 231834532 with hs1 | hs1
    · -- n < 231834532
      rcases Nat.lt_or_ge n 230755395 with hs2 | hs2
      · -- n < 230755395
        rcases Nat.lt_or_ge n 230215827 with hs3 | hs3
        · -- n < 230215827
          rcases Nat.lt_or_ge n 230035971 with hs4 | hs4
          · -- n < 230035971
            rcases Nat.lt_or_ge n 229856115 with hs5 | hs5
            · -- n < 229856115
              exact Brocard.berndt_galway_chunk_1278 n m (by omega) (by omega) h
            · -- n >= 229856115
              exact Brocard.berndt_galway_chunk_1279 n m (by omega) (by omega) h
          · -- n >= 230035971
            exact Brocard.berndt_galway_chunk_1280 n m (by omega) (by omega) h
        · -- n >= 230215827
          rcases Nat.lt_or_ge n 230575539 with hs4 | hs4
          · -- n < 230575539
            rcases Nat.lt_or_ge n 230395683 with hs5 | hs5
            · -- n < 230395683
              exact Brocard.berndt_galway_chunk_1281 n m (by omega) (by omega) h
            · -- n >= 230395683
              exact Brocard.berndt_galway_chunk_1282 n m (by omega) (by omega) h
          · -- n >= 230575539
            exact Brocard.berndt_galway_chunk_1283 n m (by omega) (by omega) h
      · -- n >= 230755395
        rcases Nat.lt_or_ge n 231294964 with hs3 | hs3
        · -- n < 231294964
          rcases Nat.lt_or_ge n 231115107 with hs4 | hs4
          · -- n < 231115107
            rcases Nat.lt_or_ge n 230935251 with hs5 | hs5
            · -- n < 230935251
              exact Brocard.berndt_galway_chunk_1284 n m (by omega) (by omega) h
            · -- n >= 230935251
              exact Brocard.berndt_galway_chunk_1285 n m (by omega) (by omega) h
          · -- n >= 231115107
            exact Brocard.berndt_galway_chunk_1286 n m (by omega) (by omega) h
        · -- n >= 231294964
          rcases Nat.lt_or_ge n 231654676 with hs4 | hs4
          · -- n < 231654676
            rcases Nat.lt_or_ge n 231474820 with hs5 | hs5
            · -- n < 231474820
              exact Brocard.berndt_galway_chunk_1287 n m (by omega) (by omega) h
            · -- n >= 231474820
              exact Brocard.berndt_galway_chunk_1288 n m (by omega) (by omega) h
          · -- n >= 231654676
            exact Brocard.berndt_galway_chunk_1289 n m (by omega) (by omega) h
    · -- n >= 231834532
      rcases Nat.lt_or_ge n 232913669 with hs2 | hs2
      · -- n < 232913669
        rcases Nat.lt_or_ge n 232374100 with hs3 | hs3
        · -- n < 232374100
          rcases Nat.lt_or_ge n 232194244 with hs4 | hs4
          · -- n < 232194244
            rcases Nat.lt_or_ge n 232014388 with hs5 | hs5
            · -- n < 232014388
              exact Brocard.berndt_galway_chunk_1290 n m (by omega) (by omega) h
            · -- n >= 232014388
              exact Brocard.berndt_galway_chunk_1291 n m (by omega) (by omega) h
          · -- n >= 232194244
            exact Brocard.berndt_galway_chunk_1292 n m (by omega) (by omega) h
        · -- n >= 232374100
          rcases Nat.lt_or_ge n 232733812 with hs4 | hs4
          · -- n < 232733812
            rcases Nat.lt_or_ge n 232553956 with hs5 | hs5
            · -- n < 232553956
              exact Brocard.berndt_galway_chunk_1293 n m (by omega) (by omega) h
            · -- n >= 232553956
              exact Brocard.berndt_galway_chunk_1294 n m (by omega) (by omega) h
          · -- n >= 232733812
            exact Brocard.berndt_galway_chunk_1295 n m (by omega) (by omega) h
      · -- n >= 232913669
        rcases Nat.lt_or_ge n 233453237 with hs3 | hs3
        · -- n < 233453237
          rcases Nat.lt_or_ge n 233273381 with hs4 | hs4
          · -- n < 233273381
            rcases Nat.lt_or_ge n 233093525 with hs5 | hs5
            · -- n < 233093525
              exact Brocard.berndt_galway_chunk_1296 n m (by omega) (by omega) h
            · -- n >= 233093525
              exact Brocard.berndt_galway_chunk_1297 n m (by omega) (by omega) h
          · -- n >= 233273381
            exact Brocard.berndt_galway_chunk_1298 n m (by omega) (by omega) h
        · -- n >= 233453237
          rcases Nat.lt_or_ge n 233633093 with hs4 | hs4
          · -- n < 233633093
            exact Brocard.berndt_galway_chunk_1299 n m (by omega) (by omega) h
          · -- n >= 233633093
            exact Brocard.berndt_galway_chunk_1300 n m (by omega) (by omega) h
