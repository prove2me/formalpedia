-- Prove2me | solution 1 for Brocard.berndt_galway_group_030
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:52:38.102972+00:00
-- url     : https://prove2.me/submissions/242b8a1d-87c5-4efe-afc2-7b9e40e7398a

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_1347
import Theorems.Thm_Brocard_berndt_galway_chunk_1348
import Theorems.Thm_Brocard_berndt_galway_chunk_1349
import Theorems.Thm_Brocard_berndt_galway_chunk_1350
import Theorems.Thm_Brocard_berndt_galway_chunk_1351
import Theorems.Thm_Brocard_berndt_galway_chunk_1352
import Theorems.Thm_Brocard_berndt_galway_chunk_1353
import Theorems.Thm_Brocard_berndt_galway_chunk_1354
import Theorems.Thm_Brocard_berndt_galway_chunk_1355
import Theorems.Thm_Brocard_berndt_galway_chunk_1356
import Theorems.Thm_Brocard_berndt_galway_chunk_1357
import Theorems.Thm_Brocard_berndt_galway_chunk_1358
import Theorems.Thm_Brocard_berndt_galway_chunk_1359
import Theorems.Thm_Brocard_berndt_galway_chunk_1360
import Theorems.Thm_Brocard_berndt_galway_chunk_1361
import Theorems.Thm_Brocard_berndt_galway_chunk_1362
import Theorems.Thm_Brocard_berndt_galway_chunk_1363
import Theorems.Thm_Brocard_berndt_galway_chunk_1364
import Theorems.Thm_Brocard_berndt_galway_chunk_1365
import Theorems.Thm_Brocard_berndt_galway_chunk_1366
import Theorems.Thm_Brocard_berndt_galway_chunk_1367
import Theorems.Thm_Brocard_berndt_galway_chunk_1368
import Theorems.Thm_Brocard_berndt_galway_chunk_1369
import Theorems.Thm_Brocard_berndt_galway_chunk_1370
import Theorems.Thm_Brocard_berndt_galway_chunk_1371
import Theorems.Thm_Brocard_berndt_galway_chunk_1372
import Theorems.Thm_Brocard_berndt_galway_chunk_1373
import Theorems.Thm_Brocard_berndt_galway_chunk_1374
import Theorems.Thm_Brocard_berndt_galway_chunk_1375
import Theorems.Thm_Brocard_berndt_galway_chunk_1376
import Theorems.Thm_Brocard_berndt_galway_chunk_1377
import Theorems.Thm_Brocard_berndt_galway_chunk_1378
import Theorems.Thm_Brocard_berndt_galway_chunk_1379
import Theorems.Thm_Brocard_berndt_galway_chunk_1380
import Theorems.Thm_Brocard_berndt_galway_chunk_1381
import Theorems.Thm_Brocard_berndt_galway_chunk_1382
import Theorems.Thm_Brocard_berndt_galway_chunk_1383
import Theorems.Thm_Brocard_berndt_galway_chunk_1384
import Theorems.Thm_Brocard_berndt_galway_chunk_1385
import Theorems.Thm_Brocard_berndt_galway_chunk_1386
import Theorems.Thm_Brocard_berndt_galway_chunk_1387
import Theorems.Thm_Brocard_berndt_galway_chunk_1388
import Theorems.Thm_Brocard_berndt_galway_chunk_1389
import Theorems.Thm_Brocard_berndt_galway_chunk_1390
import Theorems.Thm_Brocard_berndt_galway_chunk_1391
import Theorems.Thm_Brocard_berndt_galway_chunk_1392

theorem solution (n m : ℕ) (h1 : 242086330 ≤ n) (h2 : n < 250359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 246223021 with hs0 | hs0
  · -- n < 246223021
    rcases Nat.lt_or_ge n 244244604 with hs1 | hs1
    · -- n < 244244604
      rcases Nat.lt_or_ge n 243165467 with hs2 | hs2
      · -- n < 243165467
        rcases Nat.lt_or_ge n 242625899 with hs3 | hs3
        · -- n < 242625899
          rcases Nat.lt_or_ge n 242446043 with hs4 | hs4
          · -- n < 242446043
            rcases Nat.lt_or_ge n 242266187 with hs5 | hs5
            · -- n < 242266187
              exact Brocard.berndt_galway_chunk_1347 n m (by omega) (by omega) h
            · -- n >= 242266187
              exact Brocard.berndt_galway_chunk_1348 n m (by omega) (by omega) h
          · -- n >= 242446043
            exact Brocard.berndt_galway_chunk_1349 n m (by omega) (by omega) h
        · -- n >= 242625899
          rcases Nat.lt_or_ge n 242985611 with hs4 | hs4
          · -- n < 242985611
            rcases Nat.lt_or_ge n 242805755 with hs5 | hs5
            · -- n < 242805755
              exact Brocard.berndt_galway_chunk_1350 n m (by omega) (by omega) h
            · -- n >= 242805755
              exact Brocard.berndt_galway_chunk_1351 n m (by omega) (by omega) h
          · -- n >= 242985611
            exact Brocard.berndt_galway_chunk_1352 n m (by omega) (by omega) h
      · -- n >= 243165467
        rcases Nat.lt_or_ge n 243705035 with hs3 | hs3
        · -- n < 243705035
          rcases Nat.lt_or_ge n 243525179 with hs4 | hs4
          · -- n < 243525179
            rcases Nat.lt_or_ge n 243345323 with hs5 | hs5
            · -- n < 243345323
              exact Brocard.berndt_galway_chunk_1353 n m (by omega) (by omega) h
            · -- n >= 243345323
              exact Brocard.berndt_galway_chunk_1354 n m (by omega) (by omega) h
          · -- n >= 243525179
            exact Brocard.berndt_galway_chunk_1355 n m (by omega) (by omega) h
        · -- n >= 243705035
          rcases Nat.lt_or_ge n 244064748 with hs4 | hs4
          · -- n < 244064748
            rcases Nat.lt_or_ge n 243884892 with hs5 | hs5
            · -- n < 243884892
              exact Brocard.berndt_galway_chunk_1356 n m (by omega) (by omega) h
            · -- n >= 243884892
              exact Brocard.berndt_galway_chunk_1357 n m (by omega) (by omega) h
          · -- n >= 244064748
            exact Brocard.berndt_galway_chunk_1358 n m (by omega) (by omega) h
    · -- n >= 244244604
      rcases Nat.lt_or_ge n 245323741 with hs2 | hs2
      · -- n < 245323741
        rcases Nat.lt_or_ge n 244784172 with hs3 | hs3
        · -- n < 244784172
          rcases Nat.lt_or_ge n 244604316 with hs4 | hs4
          · -- n < 244604316
            rcases Nat.lt_or_ge n 244424460 with hs5 | hs5
            · -- n < 244424460
              exact Brocard.berndt_galway_chunk_1359 n m (by omega) (by omega) h
            · -- n >= 244424460
              exact Brocard.berndt_galway_chunk_1360 n m (by omega) (by omega) h
          · -- n >= 244604316
            exact Brocard.berndt_galway_chunk_1361 n m (by omega) (by omega) h
        · -- n >= 244784172
          rcases Nat.lt_or_ge n 245143884 with hs4 | hs4
          · -- n < 245143884
            rcases Nat.lt_or_ge n 244964028 with hs5 | hs5
            · -- n < 244964028
              exact Brocard.berndt_galway_chunk_1362 n m (by omega) (by omega) h
            · -- n >= 244964028
              exact Brocard.berndt_galway_chunk_1363 n m (by omega) (by omega) h
          · -- n >= 245143884
            exact Brocard.berndt_galway_chunk_1364 n m (by omega) (by omega) h
      · -- n >= 245323741
        rcases Nat.lt_or_ge n 245863309 with hs3 | hs3
        · -- n < 245863309
          rcases Nat.lt_or_ge n 245683453 with hs4 | hs4
          · -- n < 245683453
            rcases Nat.lt_or_ge n 245503597 with hs5 | hs5
            · -- n < 245503597
              exact Brocard.berndt_galway_chunk_1365 n m (by omega) (by omega) h
            · -- n >= 245503597
              exact Brocard.berndt_galway_chunk_1366 n m (by omega) (by omega) h
          · -- n >= 245683453
            exact Brocard.berndt_galway_chunk_1367 n m (by omega) (by omega) h
        · -- n >= 245863309
          rcases Nat.lt_or_ge n 246043165 with hs4 | hs4
          · -- n < 246043165
            exact Brocard.berndt_galway_chunk_1368 n m (by omega) (by omega) h
          · -- n >= 246043165
            exact Brocard.berndt_galway_chunk_1369 n m (by omega) (by omega) h
  · -- n >= 246223021
    rcases Nat.lt_or_ge n 248381294 with hs1 | hs1
    · -- n < 248381294
      rcases Nat.lt_or_ge n 247302158 with hs2 | hs2
      · -- n < 247302158
        rcases Nat.lt_or_ge n 246762589 with hs3 | hs3
        · -- n < 246762589
          rcases Nat.lt_or_ge n 246582733 with hs4 | hs4
          · -- n < 246582733
            rcases Nat.lt_or_ge n 246402877 with hs5 | hs5
            · -- n < 246402877
              exact Brocard.berndt_galway_chunk_1370 n m (by omega) (by omega) h
            · -- n >= 246402877
              exact Brocard.berndt_galway_chunk_1371 n m (by omega) (by omega) h
          · -- n >= 246582733
            exact Brocard.berndt_galway_chunk_1372 n m (by omega) (by omega) h
        · -- n >= 246762589
          rcases Nat.lt_or_ge n 247122302 with hs4 | hs4
          · -- n < 247122302
            rcases Nat.lt_or_ge n 246942446 with hs5 | hs5
            · -- n < 246942446
              exact Brocard.berndt_galway_chunk_1373 n m (by omega) (by omega) h
            · -- n >= 246942446
              exact Brocard.berndt_galway_chunk_1374 n m (by omega) (by omega) h
          · -- n >= 247122302
            exact Brocard.berndt_galway_chunk_1375 n m (by omega) (by omega) h
      · -- n >= 247302158
        rcases Nat.lt_or_ge n 247841726 with hs3 | hs3
        · -- n < 247841726
          rcases Nat.lt_or_ge n 247661870 with hs4 | hs4
          · -- n < 247661870
            rcases Nat.lt_or_ge n 247482014 with hs5 | hs5
            · -- n < 247482014
              exact Brocard.berndt_galway_chunk_1376 n m (by omega) (by omega) h
            · -- n >= 247482014
              exact Brocard.berndt_galway_chunk_1377 n m (by omega) (by omega) h
          · -- n >= 247661870
            exact Brocard.berndt_galway_chunk_1378 n m (by omega) (by omega) h
        · -- n >= 247841726
          rcases Nat.lt_or_ge n 248201438 with hs4 | hs4
          · -- n < 248201438
            rcases Nat.lt_or_ge n 248021582 with hs5 | hs5
            · -- n < 248021582
              exact Brocard.berndt_galway_chunk_1379 n m (by omega) (by omega) h
            · -- n >= 248021582
              exact Brocard.berndt_galway_chunk_1380 n m (by omega) (by omega) h
          · -- n >= 248201438
            exact Brocard.berndt_galway_chunk_1381 n m (by omega) (by omega) h
    · -- n >= 248381294
      rcases Nat.lt_or_ge n 249460431 with hs2 | hs2
      · -- n < 249460431
        rcases Nat.lt_or_ge n 248920863 with hs3 | hs3
        · -- n < 248920863
          rcases Nat.lt_or_ge n 248741007 with hs4 | hs4
          · -- n < 248741007
            rcases Nat.lt_or_ge n 248561151 with hs5 | hs5
            · -- n < 248561151
              exact Brocard.berndt_galway_chunk_1382 n m (by omega) (by omega) h
            · -- n >= 248561151
              exact Brocard.berndt_galway_chunk_1383 n m (by omega) (by omega) h
          · -- n >= 248741007
            exact Brocard.berndt_galway_chunk_1384 n m (by omega) (by omega) h
        · -- n >= 248920863
          rcases Nat.lt_or_ge n 249280575 with hs4 | hs4
          · -- n < 249280575
            rcases Nat.lt_or_ge n 249100719 with hs5 | hs5
            · -- n < 249100719
              exact Brocard.berndt_galway_chunk_1385 n m (by omega) (by omega) h
            · -- n >= 249100719
              exact Brocard.berndt_galway_chunk_1386 n m (by omega) (by omega) h
          · -- n >= 249280575
            exact Brocard.berndt_galway_chunk_1387 n m (by omega) (by omega) h
      · -- n >= 249460431
        rcases Nat.lt_or_ge n 250000000 with hs3 | hs3
        · -- n < 250000000
          rcases Nat.lt_or_ge n 249820143 with hs4 | hs4
          · -- n < 249820143
            rcases Nat.lt_or_ge n 249640287 with hs5 | hs5
            · -- n < 249640287
              exact Brocard.berndt_galway_chunk_1388 n m (by omega) (by omega) h
            · -- n >= 249640287
              exact Brocard.berndt_galway_chunk_1389 n m (by omega) (by omega) h
          · -- n >= 249820143
            exact Brocard.berndt_galway_chunk_1390 n m (by omega) (by omega) h
        · -- n >= 250000000
          rcases Nat.lt_or_ge n 250179856 with hs4 | hs4
          · -- n < 250179856
            exact Brocard.berndt_galway_chunk_1391 n m (by omega) (by omega) h
          · -- n >= 250179856
            exact Brocard.berndt_galway_chunk_1392 n m (by omega) (by omega) h
