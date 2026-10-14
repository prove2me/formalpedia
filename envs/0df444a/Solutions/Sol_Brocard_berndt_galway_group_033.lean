-- Prove2me | solution 1 for Brocard.berndt_galway_group_033
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:36:59.942037+00:00
-- url     : https://prove2.me/submissions/3a34f21c-4620-493b-bb7b-86824dcc91b1

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_1485
import Theorems.Thm_Brocard_berndt_galway_chunk_1486
import Theorems.Thm_Brocard_berndt_galway_chunk_1487
import Theorems.Thm_Brocard_berndt_galway_chunk_1488
import Theorems.Thm_Brocard_berndt_galway_chunk_1489
import Theorems.Thm_Brocard_berndt_galway_chunk_1490
import Theorems.Thm_Brocard_berndt_galway_chunk_1491
import Theorems.Thm_Brocard_berndt_galway_chunk_1492
import Theorems.Thm_Brocard_berndt_galway_chunk_1493
import Theorems.Thm_Brocard_berndt_galway_chunk_1494
import Theorems.Thm_Brocard_berndt_galway_chunk_1495
import Theorems.Thm_Brocard_berndt_galway_chunk_1496
import Theorems.Thm_Brocard_berndt_galway_chunk_1497
import Theorems.Thm_Brocard_berndt_galway_chunk_1498
import Theorems.Thm_Brocard_berndt_galway_chunk_1499
import Theorems.Thm_Brocard_berndt_galway_chunk_1500
import Theorems.Thm_Brocard_berndt_galway_chunk_1501
import Theorems.Thm_Brocard_berndt_galway_chunk_1502
import Theorems.Thm_Brocard_berndt_galway_chunk_1503
import Theorems.Thm_Brocard_berndt_galway_chunk_1504
import Theorems.Thm_Brocard_berndt_galway_chunk_1505
import Theorems.Thm_Brocard_berndt_galway_chunk_1506
import Theorems.Thm_Brocard_berndt_galway_chunk_1507
import Theorems.Thm_Brocard_berndt_galway_chunk_1508
import Theorems.Thm_Brocard_berndt_galway_chunk_1509
import Theorems.Thm_Brocard_berndt_galway_chunk_1510
import Theorems.Thm_Brocard_berndt_galway_chunk_1511
import Theorems.Thm_Brocard_berndt_galway_chunk_1512
import Theorems.Thm_Brocard_berndt_galway_chunk_1513
import Theorems.Thm_Brocard_berndt_galway_chunk_1514
import Theorems.Thm_Brocard_berndt_galway_chunk_1515
import Theorems.Thm_Brocard_berndt_galway_chunk_1516
import Theorems.Thm_Brocard_berndt_galway_chunk_1517
import Theorems.Thm_Brocard_berndt_galway_chunk_1518
import Theorems.Thm_Brocard_berndt_galway_chunk_1519
import Theorems.Thm_Brocard_berndt_galway_chunk_1520
import Theorems.Thm_Brocard_berndt_galway_chunk_1521
import Theorems.Thm_Brocard_berndt_galway_chunk_1522
import Theorems.Thm_Brocard_berndt_galway_chunk_1523
import Theorems.Thm_Brocard_berndt_galway_chunk_1524
import Theorems.Thm_Brocard_berndt_galway_chunk_1525
import Theorems.Thm_Brocard_berndt_galway_chunk_1526
import Theorems.Thm_Brocard_berndt_galway_chunk_1527
import Theorems.Thm_Brocard_berndt_galway_chunk_1528
import Theorems.Thm_Brocard_berndt_galway_chunk_1529
import Theorems.Thm_Brocard_berndt_galway_chunk_1530

theorem solution (n m : ℕ) (h1 : 266906474 ≤ n) (h2 : n < 275179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 271043165 with hs0 | hs0
  · -- n < 271043165
    rcases Nat.lt_or_ge n 269064748 with hs1 | hs1
    · -- n < 269064748
      rcases Nat.lt_or_ge n 267985611 with hs2 | hs2
      · -- n < 267985611
        rcases Nat.lt_or_ge n 267446043 with hs3 | hs3
        · -- n < 267446043
          rcases Nat.lt_or_ge n 267266187 with hs4 | hs4
          · -- n < 267266187
            rcases Nat.lt_or_ge n 267086330 with hs5 | hs5
            · -- n < 267086330
              exact Brocard.berndt_galway_chunk_1485 n m (by omega) (by omega) h
            · -- n >= 267086330
              exact Brocard.berndt_galway_chunk_1486 n m (by omega) (by omega) h
          · -- n >= 267266187
            exact Brocard.berndt_galway_chunk_1487 n m (by omega) (by omega) h
        · -- n >= 267446043
          rcases Nat.lt_or_ge n 267805755 with hs4 | hs4
          · -- n < 267805755
            rcases Nat.lt_or_ge n 267625899 with hs5 | hs5
            · -- n < 267625899
              exact Brocard.berndt_galway_chunk_1488 n m (by omega) (by omega) h
            · -- n >= 267625899
              exact Brocard.berndt_galway_chunk_1489 n m (by omega) (by omega) h
          · -- n >= 267805755
            exact Brocard.berndt_galway_chunk_1490 n m (by omega) (by omega) h
      · -- n >= 267985611
        rcases Nat.lt_or_ge n 268525179 with hs3 | hs3
        · -- n < 268525179
          rcases Nat.lt_or_ge n 268345323 with hs4 | hs4
          · -- n < 268345323
            rcases Nat.lt_or_ge n 268165467 with hs5 | hs5
            · -- n < 268165467
              exact Brocard.berndt_galway_chunk_1491 n m (by omega) (by omega) h
            · -- n >= 268165467
              exact Brocard.berndt_galway_chunk_1492 n m (by omega) (by omega) h
          · -- n >= 268345323
            exact Brocard.berndt_galway_chunk_1493 n m (by omega) (by omega) h
        · -- n >= 268525179
          rcases Nat.lt_or_ge n 268884892 with hs4 | hs4
          · -- n < 268884892
            rcases Nat.lt_or_ge n 268705035 with hs5 | hs5
            · -- n < 268705035
              exact Brocard.berndt_galway_chunk_1494 n m (by omega) (by omega) h
            · -- n >= 268705035
              exact Brocard.berndt_galway_chunk_1495 n m (by omega) (by omega) h
          · -- n >= 268884892
            exact Brocard.berndt_galway_chunk_1496 n m (by omega) (by omega) h
    · -- n >= 269064748
      rcases Nat.lt_or_ge n 270143884 with hs2 | hs2
      · -- n < 270143884
        rcases Nat.lt_or_ge n 269604316 with hs3 | hs3
        · -- n < 269604316
          rcases Nat.lt_or_ge n 269424460 with hs4 | hs4
          · -- n < 269424460
            rcases Nat.lt_or_ge n 269244604 with hs5 | hs5
            · -- n < 269244604
              exact Brocard.berndt_galway_chunk_1497 n m (by omega) (by omega) h
            · -- n >= 269244604
              exact Brocard.berndt_galway_chunk_1498 n m (by omega) (by omega) h
          · -- n >= 269424460
            exact Brocard.berndt_galway_chunk_1499 n m (by omega) (by omega) h
        · -- n >= 269604316
          rcases Nat.lt_or_ge n 269964028 with hs4 | hs4
          · -- n < 269964028
            rcases Nat.lt_or_ge n 269784172 with hs5 | hs5
            · -- n < 269784172
              exact Brocard.berndt_galway_chunk_1500 n m (by omega) (by omega) h
            · -- n >= 269784172
              exact Brocard.berndt_galway_chunk_1501 n m (by omega) (by omega) h
          · -- n >= 269964028
            exact Brocard.berndt_galway_chunk_1502 n m (by omega) (by omega) h
      · -- n >= 270143884
        rcases Nat.lt_or_ge n 270683453 with hs3 | hs3
        · -- n < 270683453
          rcases Nat.lt_or_ge n 270503597 with hs4 | hs4
          · -- n < 270503597
            rcases Nat.lt_or_ge n 270323741 with hs5 | hs5
            · -- n < 270323741
              exact Brocard.berndt_galway_chunk_1503 n m (by omega) (by omega) h
            · -- n >= 270323741
              exact Brocard.berndt_galway_chunk_1504 n m (by omega) (by omega) h
          · -- n >= 270503597
            exact Brocard.berndt_galway_chunk_1505 n m (by omega) (by omega) h
        · -- n >= 270683453
          rcases Nat.lt_or_ge n 270863309 with hs4 | hs4
          · -- n < 270863309
            exact Brocard.berndt_galway_chunk_1506 n m (by omega) (by omega) h
          · -- n >= 270863309
            exact Brocard.berndt_galway_chunk_1507 n m (by omega) (by omega) h
  · -- n >= 271043165
    rcases Nat.lt_or_ge n 273201438 with hs1 | hs1
    · -- n < 273201438
      rcases Nat.lt_or_ge n 272122302 with hs2 | hs2
      · -- n < 272122302
        rcases Nat.lt_or_ge n 271582733 with hs3 | hs3
        · -- n < 271582733
          rcases Nat.lt_or_ge n 271402877 with hs4 | hs4
          · -- n < 271402877
            rcases Nat.lt_or_ge n 271223021 with hs5 | hs5
            · -- n < 271223021
              exact Brocard.berndt_galway_chunk_1508 n m (by omega) (by omega) h
            · -- n >= 271223021
              exact Brocard.berndt_galway_chunk_1509 n m (by omega) (by omega) h
          · -- n >= 271402877
            exact Brocard.berndt_galway_chunk_1510 n m (by omega) (by omega) h
        · -- n >= 271582733
          rcases Nat.lt_or_ge n 271942446 with hs4 | hs4
          · -- n < 271942446
            rcases Nat.lt_or_ge n 271762589 with hs5 | hs5
            · -- n < 271762589
              exact Brocard.berndt_galway_chunk_1511 n m (by omega) (by omega) h
            · -- n >= 271762589
              exact Brocard.berndt_galway_chunk_1512 n m (by omega) (by omega) h
          · -- n >= 271942446
            exact Brocard.berndt_galway_chunk_1513 n m (by omega) (by omega) h
      · -- n >= 272122302
        rcases Nat.lt_or_ge n 272661870 with hs3 | hs3
        · -- n < 272661870
          rcases Nat.lt_or_ge n 272482014 with hs4 | hs4
          · -- n < 272482014
            rcases Nat.lt_or_ge n 272302158 with hs5 | hs5
            · -- n < 272302158
              exact Brocard.berndt_galway_chunk_1514 n m (by omega) (by omega) h
            · -- n >= 272302158
              exact Brocard.berndt_galway_chunk_1515 n m (by omega) (by omega) h
          · -- n >= 272482014
            exact Brocard.berndt_galway_chunk_1516 n m (by omega) (by omega) h
        · -- n >= 272661870
          rcases Nat.lt_or_ge n 273021582 with hs4 | hs4
          · -- n < 273021582
            rcases Nat.lt_or_ge n 272841726 with hs5 | hs5
            · -- n < 272841726
              exact Brocard.berndt_galway_chunk_1517 n m (by omega) (by omega) h
            · -- n >= 272841726
              exact Brocard.berndt_galway_chunk_1518 n m (by omega) (by omega) h
          · -- n >= 273021582
            exact Brocard.berndt_galway_chunk_1519 n m (by omega) (by omega) h
    · -- n >= 273201438
      rcases Nat.lt_or_ge n 274280575 with hs2 | hs2
      · -- n < 274280575
        rcases Nat.lt_or_ge n 273741007 with hs3 | hs3
        · -- n < 273741007
          rcases Nat.lt_or_ge n 273561151 with hs4 | hs4
          · -- n < 273561151
            rcases Nat.lt_or_ge n 273381294 with hs5 | hs5
            · -- n < 273381294
              exact Brocard.berndt_galway_chunk_1520 n m (by omega) (by omega) h
            · -- n >= 273381294
              exact Brocard.berndt_galway_chunk_1521 n m (by omega) (by omega) h
          · -- n >= 273561151
            exact Brocard.berndt_galway_chunk_1522 n m (by omega) (by omega) h
        · -- n >= 273741007
          rcases Nat.lt_or_ge n 274100719 with hs4 | hs4
          · -- n < 274100719
            rcases Nat.lt_or_ge n 273920863 with hs5 | hs5
            · -- n < 273920863
              exact Brocard.berndt_galway_chunk_1523 n m (by omega) (by omega) h
            · -- n >= 273920863
              exact Brocard.berndt_galway_chunk_1524 n m (by omega) (by omega) h
          · -- n >= 274100719
            exact Brocard.berndt_galway_chunk_1525 n m (by omega) (by omega) h
      · -- n >= 274280575
        rcases Nat.lt_or_ge n 274820143 with hs3 | hs3
        · -- n < 274820143
          rcases Nat.lt_or_ge n 274640287 with hs4 | hs4
          · -- n < 274640287
            rcases Nat.lt_or_ge n 274460431 with hs5 | hs5
            · -- n < 274460431
              exact Brocard.berndt_galway_chunk_1526 n m (by omega) (by omega) h
            · -- n >= 274460431
              exact Brocard.berndt_galway_chunk_1527 n m (by omega) (by omega) h
          · -- n >= 274640287
            exact Brocard.berndt_galway_chunk_1528 n m (by omega) (by omega) h
        · -- n >= 274820143
          rcases Nat.lt_or_ge n 275000000 with hs4 | hs4
          · -- n < 275000000
            exact Brocard.berndt_galway_chunk_1529 n m (by omega) (by omega) h
          · -- n >= 275000000
            exact Brocard.berndt_galway_chunk_1530 n m (by omega) (by omega) h
