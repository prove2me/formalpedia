-- Prove2me | solution 1 for Brocard.berndt_galway_group_029
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:37:44.767905+00:00
-- url     : https://prove2.me/submissions/1e65fa0b-e786-477e-a28e-f31a59067cf6

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_1301
import Theorems.Thm_Brocard_berndt_galway_chunk_1302
import Theorems.Thm_Brocard_berndt_galway_chunk_1303
import Theorems.Thm_Brocard_berndt_galway_chunk_1304
import Theorems.Thm_Brocard_berndt_galway_chunk_1305
import Theorems.Thm_Brocard_berndt_galway_chunk_1306
import Theorems.Thm_Brocard_berndt_galway_chunk_1307
import Theorems.Thm_Brocard_berndt_galway_chunk_1308
import Theorems.Thm_Brocard_berndt_galway_chunk_1309
import Theorems.Thm_Brocard_berndt_galway_chunk_1310
import Theorems.Thm_Brocard_berndt_galway_chunk_1311
import Theorems.Thm_Brocard_berndt_galway_chunk_1312
import Theorems.Thm_Brocard_berndt_galway_chunk_1313
import Theorems.Thm_Brocard_berndt_galway_chunk_1314
import Theorems.Thm_Brocard_berndt_galway_chunk_1315
import Theorems.Thm_Brocard_berndt_galway_chunk_1316
import Theorems.Thm_Brocard_berndt_galway_chunk_1317
import Theorems.Thm_Brocard_berndt_galway_chunk_1318
import Theorems.Thm_Brocard_berndt_galway_chunk_1319
import Theorems.Thm_Brocard_berndt_galway_chunk_1320
import Theorems.Thm_Brocard_berndt_galway_chunk_1321
import Theorems.Thm_Brocard_berndt_galway_chunk_1322
import Theorems.Thm_Brocard_berndt_galway_chunk_1323
import Theorems.Thm_Brocard_berndt_galway_chunk_1324
import Theorems.Thm_Brocard_berndt_galway_chunk_1325
import Theorems.Thm_Brocard_berndt_galway_chunk_1326
import Theorems.Thm_Brocard_berndt_galway_chunk_1327
import Theorems.Thm_Brocard_berndt_galway_chunk_1328
import Theorems.Thm_Brocard_berndt_galway_chunk_1329
import Theorems.Thm_Brocard_berndt_galway_chunk_1330
import Theorems.Thm_Brocard_berndt_galway_chunk_1331
import Theorems.Thm_Brocard_berndt_galway_chunk_1332
import Theorems.Thm_Brocard_berndt_galway_chunk_1333
import Theorems.Thm_Brocard_berndt_galway_chunk_1334
import Theorems.Thm_Brocard_berndt_galway_chunk_1335
import Theorems.Thm_Brocard_berndt_galway_chunk_1336
import Theorems.Thm_Brocard_berndt_galway_chunk_1337
import Theorems.Thm_Brocard_berndt_galway_chunk_1338
import Theorems.Thm_Brocard_berndt_galway_chunk_1339
import Theorems.Thm_Brocard_berndt_galway_chunk_1340
import Theorems.Thm_Brocard_berndt_galway_chunk_1341
import Theorems.Thm_Brocard_berndt_galway_chunk_1342
import Theorems.Thm_Brocard_berndt_galway_chunk_1343
import Theorems.Thm_Brocard_berndt_galway_chunk_1344
import Theorems.Thm_Brocard_berndt_galway_chunk_1345
import Theorems.Thm_Brocard_berndt_galway_chunk_1346

theorem solution (n m : ℕ) (h1 : 233812949 ≤ n) (h2 : n < 242086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 237949640 with hs0 | hs0
  · -- n < 237949640
    rcases Nat.lt_or_ge n 235971223 with hs1 | hs1
    · -- n < 235971223
      rcases Nat.lt_or_ge n 234892086 with hs2 | hs2
      · -- n < 234892086
        rcases Nat.lt_or_ge n 234352517 with hs3 | hs3
        · -- n < 234352517
          rcases Nat.lt_or_ge n 234172661 with hs4 | hs4
          · -- n < 234172661
            rcases Nat.lt_or_ge n 233992805 with hs5 | hs5
            · -- n < 233992805
              exact Brocard.berndt_galway_chunk_1301 n m (by omega) (by omega) h
            · -- n >= 233992805
              exact Brocard.berndt_galway_chunk_1302 n m (by omega) (by omega) h
          · -- n >= 234172661
            exact Brocard.berndt_galway_chunk_1303 n m (by omega) (by omega) h
        · -- n >= 234352517
          rcases Nat.lt_or_ge n 234712230 with hs4 | hs4
          · -- n < 234712230
            rcases Nat.lt_or_ge n 234532374 with hs5 | hs5
            · -- n < 234532374
              exact Brocard.berndt_galway_chunk_1304 n m (by omega) (by omega) h
            · -- n >= 234532374
              exact Brocard.berndt_galway_chunk_1305 n m (by omega) (by omega) h
          · -- n >= 234712230
            exact Brocard.berndt_galway_chunk_1306 n m (by omega) (by omega) h
      · -- n >= 234892086
        rcases Nat.lt_or_ge n 235431654 with hs3 | hs3
        · -- n < 235431654
          rcases Nat.lt_or_ge n 235251798 with hs4 | hs4
          · -- n < 235251798
            rcases Nat.lt_or_ge n 235071942 with hs5 | hs5
            · -- n < 235071942
              exact Brocard.berndt_galway_chunk_1307 n m (by omega) (by omega) h
            · -- n >= 235071942
              exact Brocard.berndt_galway_chunk_1308 n m (by omega) (by omega) h
          · -- n >= 235251798
            exact Brocard.berndt_galway_chunk_1309 n m (by omega) (by omega) h
        · -- n >= 235431654
          rcases Nat.lt_or_ge n 235791366 with hs4 | hs4
          · -- n < 235791366
            rcases Nat.lt_or_ge n 235611510 with hs5 | hs5
            · -- n < 235611510
              exact Brocard.berndt_galway_chunk_1310 n m (by omega) (by omega) h
            · -- n >= 235611510
              exact Brocard.berndt_galway_chunk_1311 n m (by omega) (by omega) h
          · -- n >= 235791366
            exact Brocard.berndt_galway_chunk_1312 n m (by omega) (by omega) h
    · -- n >= 235971223
      rcases Nat.lt_or_ge n 237050359 with hs2 | hs2
      · -- n < 237050359
        rcases Nat.lt_or_ge n 236510791 with hs3 | hs3
        · -- n < 236510791
          rcases Nat.lt_or_ge n 236330935 with hs4 | hs4
          · -- n < 236330935
            rcases Nat.lt_or_ge n 236151079 with hs5 | hs5
            · -- n < 236151079
              exact Brocard.berndt_galway_chunk_1313 n m (by omega) (by omega) h
            · -- n >= 236151079
              exact Brocard.berndt_galway_chunk_1314 n m (by omega) (by omega) h
          · -- n >= 236330935
            exact Brocard.berndt_galway_chunk_1315 n m (by omega) (by omega) h
        · -- n >= 236510791
          rcases Nat.lt_or_ge n 236870503 with hs4 | hs4
          · -- n < 236870503
            rcases Nat.lt_or_ge n 236690647 with hs5 | hs5
            · -- n < 236690647
              exact Brocard.berndt_galway_chunk_1316 n m (by omega) (by omega) h
            · -- n >= 236690647
              exact Brocard.berndt_galway_chunk_1317 n m (by omega) (by omega) h
          · -- n >= 236870503
            exact Brocard.berndt_galway_chunk_1318 n m (by omega) (by omega) h
      · -- n >= 237050359
        rcases Nat.lt_or_ge n 237589928 with hs3 | hs3
        · -- n < 237589928
          rcases Nat.lt_or_ge n 237410071 with hs4 | hs4
          · -- n < 237410071
            rcases Nat.lt_or_ge n 237230215 with hs5 | hs5
            · -- n < 237230215
              exact Brocard.berndt_galway_chunk_1319 n m (by omega) (by omega) h
            · -- n >= 237230215
              exact Brocard.berndt_galway_chunk_1320 n m (by omega) (by omega) h
          · -- n >= 237410071
            exact Brocard.berndt_galway_chunk_1321 n m (by omega) (by omega) h
        · -- n >= 237589928
          rcases Nat.lt_or_ge n 237769784 with hs4 | hs4
          · -- n < 237769784
            exact Brocard.berndt_galway_chunk_1322 n m (by omega) (by omega) h
          · -- n >= 237769784
            exact Brocard.berndt_galway_chunk_1323 n m (by omega) (by omega) h
  · -- n >= 237949640
    rcases Nat.lt_or_ge n 240107913 with hs1 | hs1
    · -- n < 240107913
      rcases Nat.lt_or_ge n 239028776 with hs2 | hs2
      · -- n < 239028776
        rcases Nat.lt_or_ge n 238489208 with hs3 | hs3
        · -- n < 238489208
          rcases Nat.lt_or_ge n 238309352 with hs4 | hs4
          · -- n < 238309352
            rcases Nat.lt_or_ge n 238129496 with hs5 | hs5
            · -- n < 238129496
              exact Brocard.berndt_galway_chunk_1324 n m (by omega) (by omega) h
            · -- n >= 238129496
              exact Brocard.berndt_galway_chunk_1325 n m (by omega) (by omega) h
          · -- n >= 238309352
            exact Brocard.berndt_galway_chunk_1326 n m (by omega) (by omega) h
        · -- n >= 238489208
          rcases Nat.lt_or_ge n 238848920 with hs4 | hs4
          · -- n < 238848920
            rcases Nat.lt_or_ge n 238669064 with hs5 | hs5
            · -- n < 238669064
              exact Brocard.berndt_galway_chunk_1327 n m (by omega) (by omega) h
            · -- n >= 238669064
              exact Brocard.berndt_galway_chunk_1328 n m (by omega) (by omega) h
          · -- n >= 238848920
            exact Brocard.berndt_galway_chunk_1329 n m (by omega) (by omega) h
      · -- n >= 239028776
        rcases Nat.lt_or_ge n 239568345 with hs3 | hs3
        · -- n < 239568345
          rcases Nat.lt_or_ge n 239388489 with hs4 | hs4
          · -- n < 239388489
            rcases Nat.lt_or_ge n 239208633 with hs5 | hs5
            · -- n < 239208633
              exact Brocard.berndt_galway_chunk_1330 n m (by omega) (by omega) h
            · -- n >= 239208633
              exact Brocard.berndt_galway_chunk_1331 n m (by omega) (by omega) h
          · -- n >= 239388489
            exact Brocard.berndt_galway_chunk_1332 n m (by omega) (by omega) h
        · -- n >= 239568345
          rcases Nat.lt_or_ge n 239928057 with hs4 | hs4
          · -- n < 239928057
            rcases Nat.lt_or_ge n 239748201 with hs5 | hs5
            · -- n < 239748201
              exact Brocard.berndt_galway_chunk_1333 n m (by omega) (by omega) h
            · -- n >= 239748201
              exact Brocard.berndt_galway_chunk_1334 n m (by omega) (by omega) h
          · -- n >= 239928057
            exact Brocard.berndt_galway_chunk_1335 n m (by omega) (by omega) h
    · -- n >= 240107913
      rcases Nat.lt_or_ge n 241187050 with hs2 | hs2
      · -- n < 241187050
        rcases Nat.lt_or_ge n 240647482 with hs3 | hs3
        · -- n < 240647482
          rcases Nat.lt_or_ge n 240467625 with hs4 | hs4
          · -- n < 240467625
            rcases Nat.lt_or_ge n 240287769 with hs5 | hs5
            · -- n < 240287769
              exact Brocard.berndt_galway_chunk_1336 n m (by omega) (by omega) h
            · -- n >= 240287769
              exact Brocard.berndt_galway_chunk_1337 n m (by omega) (by omega) h
          · -- n >= 240467625
            exact Brocard.berndt_galway_chunk_1338 n m (by omega) (by omega) h
        · -- n >= 240647482
          rcases Nat.lt_or_ge n 241007194 with hs4 | hs4
          · -- n < 241007194
            rcases Nat.lt_or_ge n 240827338 with hs5 | hs5
            · -- n < 240827338
              exact Brocard.berndt_galway_chunk_1339 n m (by omega) (by omega) h
            · -- n >= 240827338
              exact Brocard.berndt_galway_chunk_1340 n m (by omega) (by omega) h
          · -- n >= 241007194
            exact Brocard.berndt_galway_chunk_1341 n m (by omega) (by omega) h
      · -- n >= 241187050
        rcases Nat.lt_or_ge n 241726618 with hs3 | hs3
        · -- n < 241726618
          rcases Nat.lt_or_ge n 241546762 with hs4 | hs4
          · -- n < 241546762
            rcases Nat.lt_or_ge n 241366906 with hs5 | hs5
            · -- n < 241366906
              exact Brocard.berndt_galway_chunk_1342 n m (by omega) (by omega) h
            · -- n >= 241366906
              exact Brocard.berndt_galway_chunk_1343 n m (by omega) (by omega) h
          · -- n >= 241546762
            exact Brocard.berndt_galway_chunk_1344 n m (by omega) (by omega) h
        · -- n >= 241726618
          rcases Nat.lt_or_ge n 241906474 with hs4 | hs4
          · -- n < 241906474
            exact Brocard.berndt_galway_chunk_1345 n m (by omega) (by omega) h
          · -- n >= 241906474
            exact Brocard.berndt_galway_chunk_1346 n m (by omega) (by omega) h
