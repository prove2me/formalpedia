-- Prove2me | solution 1 for Brocard.berndt_galway_group_032
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:23:20.614032+00:00
-- url     : https://prove2.me/submissions/fb59b973-fbe9-4064-8e31-004f1d8040ca

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_1439
import Theorems.Thm_Brocard_berndt_galway_chunk_1440
import Theorems.Thm_Brocard_berndt_galway_chunk_1441
import Theorems.Thm_Brocard_berndt_galway_chunk_1442
import Theorems.Thm_Brocard_berndt_galway_chunk_1443
import Theorems.Thm_Brocard_berndt_galway_chunk_1444
import Theorems.Thm_Brocard_berndt_galway_chunk_1445
import Theorems.Thm_Brocard_berndt_galway_chunk_1446
import Theorems.Thm_Brocard_berndt_galway_chunk_1447
import Theorems.Thm_Brocard_berndt_galway_chunk_1448
import Theorems.Thm_Brocard_berndt_galway_chunk_1449
import Theorems.Thm_Brocard_berndt_galway_chunk_1450
import Theorems.Thm_Brocard_berndt_galway_chunk_1451
import Theorems.Thm_Brocard_berndt_galway_chunk_1452
import Theorems.Thm_Brocard_berndt_galway_chunk_1453
import Theorems.Thm_Brocard_berndt_galway_chunk_1454
import Theorems.Thm_Brocard_berndt_galway_chunk_1455
import Theorems.Thm_Brocard_berndt_galway_chunk_1456
import Theorems.Thm_Brocard_berndt_galway_chunk_1457
import Theorems.Thm_Brocard_berndt_galway_chunk_1458
import Theorems.Thm_Brocard_berndt_galway_chunk_1459
import Theorems.Thm_Brocard_berndt_galway_chunk_1460
import Theorems.Thm_Brocard_berndt_galway_chunk_1461
import Theorems.Thm_Brocard_berndt_galway_chunk_1462
import Theorems.Thm_Brocard_berndt_galway_chunk_1463
import Theorems.Thm_Brocard_berndt_galway_chunk_1464
import Theorems.Thm_Brocard_berndt_galway_chunk_1465
import Theorems.Thm_Brocard_berndt_galway_chunk_1466
import Theorems.Thm_Brocard_berndt_galway_chunk_1467
import Theorems.Thm_Brocard_berndt_galway_chunk_1468
import Theorems.Thm_Brocard_berndt_galway_chunk_1469
import Theorems.Thm_Brocard_berndt_galway_chunk_1470
import Theorems.Thm_Brocard_berndt_galway_chunk_1471
import Theorems.Thm_Brocard_berndt_galway_chunk_1472
import Theorems.Thm_Brocard_berndt_galway_chunk_1473
import Theorems.Thm_Brocard_berndt_galway_chunk_1474
import Theorems.Thm_Brocard_berndt_galway_chunk_1475
import Theorems.Thm_Brocard_berndt_galway_chunk_1476
import Theorems.Thm_Brocard_berndt_galway_chunk_1477
import Theorems.Thm_Brocard_berndt_galway_chunk_1478
import Theorems.Thm_Brocard_berndt_galway_chunk_1479
import Theorems.Thm_Brocard_berndt_galway_chunk_1480
import Theorems.Thm_Brocard_berndt_galway_chunk_1481
import Theorems.Thm_Brocard_berndt_galway_chunk_1482
import Theorems.Thm_Brocard_berndt_galway_chunk_1483
import Theorems.Thm_Brocard_berndt_galway_chunk_1484

theorem solution (n m : ℕ) (h1 : 258633093 ≤ n) (h2 : n < 266906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 262769784 with hs0 | hs0
  · -- n < 262769784
    rcases Nat.lt_or_ge n 260791366 with hs1 | hs1
    · -- n < 260791366
      rcases Nat.lt_or_ge n 259712230 with hs2 | hs2
      · -- n < 259712230
        rcases Nat.lt_or_ge n 259172661 with hs3 | hs3
        · -- n < 259172661
          rcases Nat.lt_or_ge n 258992805 with hs4 | hs4
          · -- n < 258992805
            rcases Nat.lt_or_ge n 258812949 with hs5 | hs5
            · -- n < 258812949
              exact Brocard.berndt_galway_chunk_1439 n m (by omega) (by omega) h
            · -- n >= 258812949
              exact Brocard.berndt_galway_chunk_1440 n m (by omega) (by omega) h
          · -- n >= 258992805
            exact Brocard.berndt_galway_chunk_1441 n m (by omega) (by omega) h
        · -- n >= 259172661
          rcases Nat.lt_or_ge n 259532374 with hs4 | hs4
          · -- n < 259532374
            rcases Nat.lt_or_ge n 259352517 with hs5 | hs5
            · -- n < 259352517
              exact Brocard.berndt_galway_chunk_1442 n m (by omega) (by omega) h
            · -- n >= 259352517
              exact Brocard.berndt_galway_chunk_1443 n m (by omega) (by omega) h
          · -- n >= 259532374
            exact Brocard.berndt_galway_chunk_1444 n m (by omega) (by omega) h
      · -- n >= 259712230
        rcases Nat.lt_or_ge n 260251798 with hs3 | hs3
        · -- n < 260251798
          rcases Nat.lt_or_ge n 260071942 with hs4 | hs4
          · -- n < 260071942
            rcases Nat.lt_or_ge n 259892086 with hs5 | hs5
            · -- n < 259892086
              exact Brocard.berndt_galway_chunk_1445 n m (by omega) (by omega) h
            · -- n >= 259892086
              exact Brocard.berndt_galway_chunk_1446 n m (by omega) (by omega) h
          · -- n >= 260071942
            exact Brocard.berndt_galway_chunk_1447 n m (by omega) (by omega) h
        · -- n >= 260251798
          rcases Nat.lt_or_ge n 260611510 with hs4 | hs4
          · -- n < 260611510
            rcases Nat.lt_or_ge n 260431654 with hs5 | hs5
            · -- n < 260431654
              exact Brocard.berndt_galway_chunk_1448 n m (by omega) (by omega) h
            · -- n >= 260431654
              exact Brocard.berndt_galway_chunk_1449 n m (by omega) (by omega) h
          · -- n >= 260611510
            exact Brocard.berndt_galway_chunk_1450 n m (by omega) (by omega) h
    · -- n >= 260791366
      rcases Nat.lt_or_ge n 261870503 with hs2 | hs2
      · -- n < 261870503
        rcases Nat.lt_or_ge n 261330935 with hs3 | hs3
        · -- n < 261330935
          rcases Nat.lt_or_ge n 261151079 with hs4 | hs4
          · -- n < 261151079
            rcases Nat.lt_or_ge n 260971223 with hs5 | hs5
            · -- n < 260971223
              exact Brocard.berndt_galway_chunk_1451 n m (by omega) (by omega) h
            · -- n >= 260971223
              exact Brocard.berndt_galway_chunk_1452 n m (by omega) (by omega) h
          · -- n >= 261151079
            exact Brocard.berndt_galway_chunk_1453 n m (by omega) (by omega) h
        · -- n >= 261330935
          rcases Nat.lt_or_ge n 261690647 with hs4 | hs4
          · -- n < 261690647
            rcases Nat.lt_or_ge n 261510791 with hs5 | hs5
            · -- n < 261510791
              exact Brocard.berndt_galway_chunk_1454 n m (by omega) (by omega) h
            · -- n >= 261510791
              exact Brocard.berndt_galway_chunk_1455 n m (by omega) (by omega) h
          · -- n >= 261690647
            exact Brocard.berndt_galway_chunk_1456 n m (by omega) (by omega) h
      · -- n >= 261870503
        rcases Nat.lt_or_ge n 262410071 with hs3 | hs3
        · -- n < 262410071
          rcases Nat.lt_or_ge n 262230215 with hs4 | hs4
          · -- n < 262230215
            rcases Nat.lt_or_ge n 262050359 with hs5 | hs5
            · -- n < 262050359
              exact Brocard.berndt_galway_chunk_1457 n m (by omega) (by omega) h
            · -- n >= 262050359
              exact Brocard.berndt_galway_chunk_1458 n m (by omega) (by omega) h
          · -- n >= 262230215
            exact Brocard.berndt_galway_chunk_1459 n m (by omega) (by omega) h
        · -- n >= 262410071
          rcases Nat.lt_or_ge n 262589928 with hs4 | hs4
          · -- n < 262589928
            exact Brocard.berndt_galway_chunk_1460 n m (by omega) (by omega) h
          · -- n >= 262589928
            exact Brocard.berndt_galway_chunk_1461 n m (by omega) (by omega) h
  · -- n >= 262769784
    rcases Nat.lt_or_ge n 264928057 with hs1 | hs1
    · -- n < 264928057
      rcases Nat.lt_or_ge n 263848920 with hs2 | hs2
      · -- n < 263848920
        rcases Nat.lt_or_ge n 263309352 with hs3 | hs3
        · -- n < 263309352
          rcases Nat.lt_or_ge n 263129496 with hs4 | hs4
          · -- n < 263129496
            rcases Nat.lt_or_ge n 262949640 with hs5 | hs5
            · -- n < 262949640
              exact Brocard.berndt_galway_chunk_1462 n m (by omega) (by omega) h
            · -- n >= 262949640
              exact Brocard.berndt_galway_chunk_1463 n m (by omega) (by omega) h
          · -- n >= 263129496
            exact Brocard.berndt_galway_chunk_1464 n m (by omega) (by omega) h
        · -- n >= 263309352
          rcases Nat.lt_or_ge n 263669064 with hs4 | hs4
          · -- n < 263669064
            rcases Nat.lt_or_ge n 263489208 with hs5 | hs5
            · -- n < 263489208
              exact Brocard.berndt_galway_chunk_1465 n m (by omega) (by omega) h
            · -- n >= 263489208
              exact Brocard.berndt_galway_chunk_1466 n m (by omega) (by omega) h
          · -- n >= 263669064
            exact Brocard.berndt_galway_chunk_1467 n m (by omega) (by omega) h
      · -- n >= 263848920
        rcases Nat.lt_or_ge n 264388489 with hs3 | hs3
        · -- n < 264388489
          rcases Nat.lt_or_ge n 264208633 with hs4 | hs4
          · -- n < 264208633
            rcases Nat.lt_or_ge n 264028776 with hs5 | hs5
            · -- n < 264028776
              exact Brocard.berndt_galway_chunk_1468 n m (by omega) (by omega) h
            · -- n >= 264028776
              exact Brocard.berndt_galway_chunk_1469 n m (by omega) (by omega) h
          · -- n >= 264208633
            exact Brocard.berndt_galway_chunk_1470 n m (by omega) (by omega) h
        · -- n >= 264388489
          rcases Nat.lt_or_ge n 264748201 with hs4 | hs4
          · -- n < 264748201
            rcases Nat.lt_or_ge n 264568345 with hs5 | hs5
            · -- n < 264568345
              exact Brocard.berndt_galway_chunk_1471 n m (by omega) (by omega) h
            · -- n >= 264568345
              exact Brocard.berndt_galway_chunk_1472 n m (by omega) (by omega) h
          · -- n >= 264748201
            exact Brocard.berndt_galway_chunk_1473 n m (by omega) (by omega) h
    · -- n >= 264928057
      rcases Nat.lt_or_ge n 266007194 with hs2 | hs2
      · -- n < 266007194
        rcases Nat.lt_or_ge n 265467625 with hs3 | hs3
        · -- n < 265467625
          rcases Nat.lt_or_ge n 265287769 with hs4 | hs4
          · -- n < 265287769
            rcases Nat.lt_or_ge n 265107913 with hs5 | hs5
            · -- n < 265107913
              exact Brocard.berndt_galway_chunk_1474 n m (by omega) (by omega) h
            · -- n >= 265107913
              exact Brocard.berndt_galway_chunk_1475 n m (by omega) (by omega) h
          · -- n >= 265287769
            exact Brocard.berndt_galway_chunk_1476 n m (by omega) (by omega) h
        · -- n >= 265467625
          rcases Nat.lt_or_ge n 265827338 with hs4 | hs4
          · -- n < 265827338
            rcases Nat.lt_or_ge n 265647482 with hs5 | hs5
            · -- n < 265647482
              exact Brocard.berndt_galway_chunk_1477 n m (by omega) (by omega) h
            · -- n >= 265647482
              exact Brocard.berndt_galway_chunk_1478 n m (by omega) (by omega) h
          · -- n >= 265827338
            exact Brocard.berndt_galway_chunk_1479 n m (by omega) (by omega) h
      · -- n >= 266007194
        rcases Nat.lt_or_ge n 266546762 with hs3 | hs3
        · -- n < 266546762
          rcases Nat.lt_or_ge n 266366906 with hs4 | hs4
          · -- n < 266366906
            rcases Nat.lt_or_ge n 266187050 with hs5 | hs5
            · -- n < 266187050
              exact Brocard.berndt_galway_chunk_1480 n m (by omega) (by omega) h
            · -- n >= 266187050
              exact Brocard.berndt_galway_chunk_1481 n m (by omega) (by omega) h
          · -- n >= 266366906
            exact Brocard.berndt_galway_chunk_1482 n m (by omega) (by omega) h
        · -- n >= 266546762
          rcases Nat.lt_or_ge n 266726618 with hs4 | hs4
          · -- n < 266726618
            exact Brocard.berndt_galway_chunk_1483 n m (by omega) (by omega) h
          · -- n >= 266726618
            exact Brocard.berndt_galway_chunk_1484 n m (by omega) (by omega) h
