-- Prove2me | solution 1 for Brocard.berndt_galway_group_031
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:06:47.564165+00:00
-- url     : https://prove2.me/submissions/93b2ff37-e33a-4023-8ea3-9fac4b7d3d10

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_1393
import Theorems.Thm_Brocard_berndt_galway_chunk_1394
import Theorems.Thm_Brocard_berndt_galway_chunk_1395
import Theorems.Thm_Brocard_berndt_galway_chunk_1396
import Theorems.Thm_Brocard_berndt_galway_chunk_1397
import Theorems.Thm_Brocard_berndt_galway_chunk_1398
import Theorems.Thm_Brocard_berndt_galway_chunk_1399
import Theorems.Thm_Brocard_berndt_galway_chunk_1400
import Theorems.Thm_Brocard_berndt_galway_chunk_1401
import Theorems.Thm_Brocard_berndt_galway_chunk_1402
import Theorems.Thm_Brocard_berndt_galway_chunk_1403
import Theorems.Thm_Brocard_berndt_galway_chunk_1404
import Theorems.Thm_Brocard_berndt_galway_chunk_1405
import Theorems.Thm_Brocard_berndt_galway_chunk_1406
import Theorems.Thm_Brocard_berndt_galway_chunk_1407
import Theorems.Thm_Brocard_berndt_galway_chunk_1408
import Theorems.Thm_Brocard_berndt_galway_chunk_1409
import Theorems.Thm_Brocard_berndt_galway_chunk_1410
import Theorems.Thm_Brocard_berndt_galway_chunk_1411
import Theorems.Thm_Brocard_berndt_galway_chunk_1412
import Theorems.Thm_Brocard_berndt_galway_chunk_1413
import Theorems.Thm_Brocard_berndt_galway_chunk_1414
import Theorems.Thm_Brocard_berndt_galway_chunk_1415
import Theorems.Thm_Brocard_berndt_galway_chunk_1416
import Theorems.Thm_Brocard_berndt_galway_chunk_1417
import Theorems.Thm_Brocard_berndt_galway_chunk_1418
import Theorems.Thm_Brocard_berndt_galway_chunk_1419
import Theorems.Thm_Brocard_berndt_galway_chunk_1420
import Theorems.Thm_Brocard_berndt_galway_chunk_1421
import Theorems.Thm_Brocard_berndt_galway_chunk_1422
import Theorems.Thm_Brocard_berndt_galway_chunk_1423
import Theorems.Thm_Brocard_berndt_galway_chunk_1424
import Theorems.Thm_Brocard_berndt_galway_chunk_1425
import Theorems.Thm_Brocard_berndt_galway_chunk_1426
import Theorems.Thm_Brocard_berndt_galway_chunk_1427
import Theorems.Thm_Brocard_berndt_galway_chunk_1428
import Theorems.Thm_Brocard_berndt_galway_chunk_1429
import Theorems.Thm_Brocard_berndt_galway_chunk_1430
import Theorems.Thm_Brocard_berndt_galway_chunk_1431
import Theorems.Thm_Brocard_berndt_galway_chunk_1432
import Theorems.Thm_Brocard_berndt_galway_chunk_1433
import Theorems.Thm_Brocard_berndt_galway_chunk_1434
import Theorems.Thm_Brocard_berndt_galway_chunk_1435
import Theorems.Thm_Brocard_berndt_galway_chunk_1436
import Theorems.Thm_Brocard_berndt_galway_chunk_1437
import Theorems.Thm_Brocard_berndt_galway_chunk_1438

theorem solution (n m : ℕ) (h1 : 250359712 ≤ n) (h2 : n < 258633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 254496402 with hs0 | hs0
  · -- n < 254496402
    rcases Nat.lt_or_ge n 252517985 with hs1 | hs1
    · -- n < 252517985
      rcases Nat.lt_or_ge n 251438848 with hs2 | hs2
      · -- n < 251438848
        rcases Nat.lt_or_ge n 250899280 with hs3 | hs3
        · -- n < 250899280
          rcases Nat.lt_or_ge n 250719424 with hs4 | hs4
          · -- n < 250719424
            rcases Nat.lt_or_ge n 250539568 with hs5 | hs5
            · -- n < 250539568
              exact Brocard.berndt_galway_chunk_1393 n m (by omega) (by omega) h
            · -- n >= 250539568
              exact Brocard.berndt_galway_chunk_1394 n m (by omega) (by omega) h
          · -- n >= 250719424
            exact Brocard.berndt_galway_chunk_1395 n m (by omega) (by omega) h
        · -- n >= 250899280
          rcases Nat.lt_or_ge n 251258992 with hs4 | hs4
          · -- n < 251258992
            rcases Nat.lt_or_ge n 251079136 with hs5 | hs5
            · -- n < 251079136
              exact Brocard.berndt_galway_chunk_1396 n m (by omega) (by omega) h
            · -- n >= 251079136
              exact Brocard.berndt_galway_chunk_1397 n m (by omega) (by omega) h
          · -- n >= 251258992
            exact Brocard.berndt_galway_chunk_1398 n m (by omega) (by omega) h
      · -- n >= 251438848
        rcases Nat.lt_or_ge n 251978417 with hs3 | hs3
        · -- n < 251978417
          rcases Nat.lt_or_ge n 251798561 with hs4 | hs4
          · -- n < 251798561
            rcases Nat.lt_or_ge n 251618705 with hs5 | hs5
            · -- n < 251618705
              exact Brocard.berndt_galway_chunk_1399 n m (by omega) (by omega) h
            · -- n >= 251618705
              exact Brocard.berndt_galway_chunk_1400 n m (by omega) (by omega) h
          · -- n >= 251798561
            exact Brocard.berndt_galway_chunk_1401 n m (by omega) (by omega) h
        · -- n >= 251978417
          rcases Nat.lt_or_ge n 252338129 with hs4 | hs4
          · -- n < 252338129
            rcases Nat.lt_or_ge n 252158273 with hs5 | hs5
            · -- n < 252158273
              exact Brocard.berndt_galway_chunk_1402 n m (by omega) (by omega) h
            · -- n >= 252158273
              exact Brocard.berndt_galway_chunk_1403 n m (by omega) (by omega) h
          · -- n >= 252338129
            exact Brocard.berndt_galway_chunk_1404 n m (by omega) (by omega) h
    · -- n >= 252517985
      rcases Nat.lt_or_ge n 253597122 with hs2 | hs2
      · -- n < 253597122
        rcases Nat.lt_or_ge n 253057553 with hs3 | hs3
        · -- n < 253057553
          rcases Nat.lt_or_ge n 252877697 with hs4 | hs4
          · -- n < 252877697
            rcases Nat.lt_or_ge n 252697841 with hs5 | hs5
            · -- n < 252697841
              exact Brocard.berndt_galway_chunk_1405 n m (by omega) (by omega) h
            · -- n >= 252697841
              exact Brocard.berndt_galway_chunk_1406 n m (by omega) (by omega) h
          · -- n >= 252877697
            exact Brocard.berndt_galway_chunk_1407 n m (by omega) (by omega) h
        · -- n >= 253057553
          rcases Nat.lt_or_ge n 253417266 with hs4 | hs4
          · -- n < 253417266
            rcases Nat.lt_or_ge n 253237410 with hs5 | hs5
            · -- n < 253237410
              exact Brocard.berndt_galway_chunk_1408 n m (by omega) (by omega) h
            · -- n >= 253237410
              exact Brocard.berndt_galway_chunk_1409 n m (by omega) (by omega) h
          · -- n >= 253417266
            exact Brocard.berndt_galway_chunk_1410 n m (by omega) (by omega) h
      · -- n >= 253597122
        rcases Nat.lt_or_ge n 254136690 with hs3 | hs3
        · -- n < 254136690
          rcases Nat.lt_or_ge n 253956834 with hs4 | hs4
          · -- n < 253956834
            rcases Nat.lt_or_ge n 253776978 with hs5 | hs5
            · -- n < 253776978
              exact Brocard.berndt_galway_chunk_1411 n m (by omega) (by omega) h
            · -- n >= 253776978
              exact Brocard.berndt_galway_chunk_1412 n m (by omega) (by omega) h
          · -- n >= 253956834
            exact Brocard.berndt_galway_chunk_1413 n m (by omega) (by omega) h
        · -- n >= 254136690
          rcases Nat.lt_or_ge n 254316546 with hs4 | hs4
          · -- n < 254316546
            exact Brocard.berndt_galway_chunk_1414 n m (by omega) (by omega) h
          · -- n >= 254316546
            exact Brocard.berndt_galway_chunk_1415 n m (by omega) (by omega) h
  · -- n >= 254496402
    rcases Nat.lt_or_ge n 256654676 with hs1 | hs1
    · -- n < 256654676
      rcases Nat.lt_or_ge n 255575539 with hs2 | hs2
      · -- n < 255575539
        rcases Nat.lt_or_ge n 255035971 with hs3 | hs3
        · -- n < 255035971
          rcases Nat.lt_or_ge n 254856115 with hs4 | hs4
          · -- n < 254856115
            rcases Nat.lt_or_ge n 254676258 with hs5 | hs5
            · -- n < 254676258
              exact Brocard.berndt_galway_chunk_1416 n m (by omega) (by omega) h
            · -- n >= 254676258
              exact Brocard.berndt_galway_chunk_1417 n m (by omega) (by omega) h
          · -- n >= 254856115
            exact Brocard.berndt_galway_chunk_1418 n m (by omega) (by omega) h
        · -- n >= 255035971
          rcases Nat.lt_or_ge n 255395683 with hs4 | hs4
          · -- n < 255395683
            rcases Nat.lt_or_ge n 255215827 with hs5 | hs5
            · -- n < 255215827
              exact Brocard.berndt_galway_chunk_1419 n m (by omega) (by omega) h
            · -- n >= 255215827
              exact Brocard.berndt_galway_chunk_1420 n m (by omega) (by omega) h
          · -- n >= 255395683
            exact Brocard.berndt_galway_chunk_1421 n m (by omega) (by omega) h
      · -- n >= 255575539
        rcases Nat.lt_or_ge n 256115107 with hs3 | hs3
        · -- n < 256115107
          rcases Nat.lt_or_ge n 255935251 with hs4 | hs4
          · -- n < 255935251
            rcases Nat.lt_or_ge n 255755395 with hs5 | hs5
            · -- n < 255755395
              exact Brocard.berndt_galway_chunk_1422 n m (by omega) (by omega) h
            · -- n >= 255755395
              exact Brocard.berndt_galway_chunk_1423 n m (by omega) (by omega) h
          · -- n >= 255935251
            exact Brocard.berndt_galway_chunk_1424 n m (by omega) (by omega) h
        · -- n >= 256115107
          rcases Nat.lt_or_ge n 256474820 with hs4 | hs4
          · -- n < 256474820
            rcases Nat.lt_or_ge n 256294964 with hs5 | hs5
            · -- n < 256294964
              exact Brocard.berndt_galway_chunk_1425 n m (by omega) (by omega) h
            · -- n >= 256294964
              exact Brocard.berndt_galway_chunk_1426 n m (by omega) (by omega) h
          · -- n >= 256474820
            exact Brocard.berndt_galway_chunk_1427 n m (by omega) (by omega) h
    · -- n >= 256654676
      rcases Nat.lt_or_ge n 257733812 with hs2 | hs2
      · -- n < 257733812
        rcases Nat.lt_or_ge n 257194244 with hs3 | hs3
        · -- n < 257194244
          rcases Nat.lt_or_ge n 257014388 with hs4 | hs4
          · -- n < 257014388
            rcases Nat.lt_or_ge n 256834532 with hs5 | hs5
            · -- n < 256834532
              exact Brocard.berndt_galway_chunk_1428 n m (by omega) (by omega) h
            · -- n >= 256834532
              exact Brocard.berndt_galway_chunk_1429 n m (by omega) (by omega) h
          · -- n >= 257014388
            exact Brocard.berndt_galway_chunk_1430 n m (by omega) (by omega) h
        · -- n >= 257194244
          rcases Nat.lt_or_ge n 257553956 with hs4 | hs4
          · -- n < 257553956
            rcases Nat.lt_or_ge n 257374100 with hs5 | hs5
            · -- n < 257374100
              exact Brocard.berndt_galway_chunk_1431 n m (by omega) (by omega) h
            · -- n >= 257374100
              exact Brocard.berndt_galway_chunk_1432 n m (by omega) (by omega) h
          · -- n >= 257553956
            exact Brocard.berndt_galway_chunk_1433 n m (by omega) (by omega) h
      · -- n >= 257733812
        rcases Nat.lt_or_ge n 258273381 with hs3 | hs3
        · -- n < 258273381
          rcases Nat.lt_or_ge n 258093525 with hs4 | hs4
          · -- n < 258093525
            rcases Nat.lt_or_ge n 257913669 with hs5 | hs5
            · -- n < 257913669
              exact Brocard.berndt_galway_chunk_1434 n m (by omega) (by omega) h
            · -- n >= 257913669
              exact Brocard.berndt_galway_chunk_1435 n m (by omega) (by omega) h
          · -- n >= 258093525
            exact Brocard.berndt_galway_chunk_1436 n m (by omega) (by omega) h
        · -- n >= 258273381
          rcases Nat.lt_or_ge n 258453237 with hs4 | hs4
          · -- n < 258453237
            exact Brocard.berndt_galway_chunk_1437 n m (by omega) (by omega) h
          · -- n >= 258453237
            exact Brocard.berndt_galway_chunk_1438 n m (by omega) (by omega) h
