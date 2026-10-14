-- Prove2me | solution 1 for Brocard.berndt_galway_group_012
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:37:08.961922+00:00
-- url     : https://prove2.me/submissions/80c3d62d-d4b3-4438-8190-42aaf57abfe0

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_0511
import Theorems.Thm_Brocard_berndt_galway_chunk_0512
import Theorems.Thm_Brocard_berndt_galway_chunk_0513
import Theorems.Thm_Brocard_berndt_galway_chunk_0514
import Theorems.Thm_Brocard_berndt_galway_chunk_0515
import Theorems.Thm_Brocard_berndt_galway_chunk_0516
import Theorems.Thm_Brocard_berndt_galway_chunk_0517
import Theorems.Thm_Brocard_berndt_galway_chunk_0518
import Theorems.Thm_Brocard_berndt_galway_chunk_0519
import Theorems.Thm_Brocard_berndt_galway_chunk_0520
import Theorems.Thm_Brocard_berndt_galway_chunk_0521
import Theorems.Thm_Brocard_berndt_galway_chunk_0522
import Theorems.Thm_Brocard_berndt_galway_chunk_0523
import Theorems.Thm_Brocard_berndt_galway_chunk_0524
import Theorems.Thm_Brocard_berndt_galway_chunk_0525
import Theorems.Thm_Brocard_berndt_galway_chunk_0526
import Theorems.Thm_Brocard_berndt_galway_chunk_0527
import Theorems.Thm_Brocard_berndt_galway_chunk_0528
import Theorems.Thm_Brocard_berndt_galway_chunk_0529
import Theorems.Thm_Brocard_berndt_galway_chunk_0530
import Theorems.Thm_Brocard_berndt_galway_chunk_0531
import Theorems.Thm_Brocard_berndt_galway_chunk_0532
import Theorems.Thm_Brocard_berndt_galway_chunk_0533
import Theorems.Thm_Brocard_berndt_galway_chunk_0534
import Theorems.Thm_Brocard_berndt_galway_chunk_0535
import Theorems.Thm_Brocard_berndt_galway_chunk_0536
import Theorems.Thm_Brocard_berndt_galway_chunk_0537
import Theorems.Thm_Brocard_berndt_galway_chunk_0538
import Theorems.Thm_Brocard_berndt_galway_chunk_0539
import Theorems.Thm_Brocard_berndt_galway_chunk_0540
import Theorems.Thm_Brocard_berndt_galway_chunk_0541
import Theorems.Thm_Brocard_berndt_galway_chunk_0542
import Theorems.Thm_Brocard_berndt_galway_chunk_0543
import Theorems.Thm_Brocard_berndt_galway_chunk_0544
import Theorems.Thm_Brocard_berndt_galway_chunk_0545
import Theorems.Thm_Brocard_berndt_galway_chunk_0546
import Theorems.Thm_Brocard_berndt_galway_chunk_0547
import Theorems.Thm_Brocard_berndt_galway_chunk_0548
import Theorems.Thm_Brocard_berndt_galway_chunk_0549
import Theorems.Thm_Brocard_berndt_galway_chunk_0550
import Theorems.Thm_Brocard_berndt_galway_chunk_0551
import Theorems.Thm_Brocard_berndt_galway_chunk_0552
import Theorems.Thm_Brocard_berndt_galway_chunk_0553
import Theorems.Thm_Brocard_berndt_galway_chunk_0554
import Theorems.Thm_Brocard_berndt_galway_chunk_0555
import Theorems.Thm_Brocard_berndt_galway_chunk_0556

theorem solution (n m : ℕ) (h1 : 91726619 ≤ n) (h2 : n < 100000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 95863309 with hs0 | hs0
  · -- n < 95863309
    rcases Nat.lt_or_ge n 93884892 with hs1 | hs1
    · -- n < 93884892
      rcases Nat.lt_or_ge n 92805755 with hs2 | hs2
      · -- n < 92805755
        rcases Nat.lt_or_ge n 92266187 with hs3 | hs3
        · -- n < 92266187
          rcases Nat.lt_or_ge n 92086331 with hs4 | hs4
          · -- n < 92086331
            rcases Nat.lt_or_ge n 91906475 with hs5 | hs5
            · -- n < 91906475
              exact Brocard.berndt_galway_chunk_0511 n m (by omega) (by omega) h
            · -- n >= 91906475
              exact Brocard.berndt_galway_chunk_0512 n m (by omega) (by omega) h
          · -- n >= 92086331
            exact Brocard.berndt_galway_chunk_0513 n m (by omega) (by omega) h
        · -- n >= 92266187
          rcases Nat.lt_or_ge n 92625899 with hs4 | hs4
          · -- n < 92625899
            rcases Nat.lt_or_ge n 92446043 with hs5 | hs5
            · -- n < 92446043
              exact Brocard.berndt_galway_chunk_0514 n m (by omega) (by omega) h
            · -- n >= 92446043
              exact Brocard.berndt_galway_chunk_0515 n m (by omega) (by omega) h
          · -- n >= 92625899
            exact Brocard.berndt_galway_chunk_0516 n m (by omega) (by omega) h
      · -- n >= 92805755
        rcases Nat.lt_or_ge n 93345324 with hs3 | hs3
        · -- n < 93345324
          rcases Nat.lt_or_ge n 93165468 with hs4 | hs4
          · -- n < 93165468
            rcases Nat.lt_or_ge n 92985612 with hs5 | hs5
            · -- n < 92985612
              exact Brocard.berndt_galway_chunk_0517 n m (by omega) (by omega) h
            · -- n >= 92985612
              exact Brocard.berndt_galway_chunk_0518 n m (by omega) (by omega) h
          · -- n >= 93165468
            exact Brocard.berndt_galway_chunk_0519 n m (by omega) (by omega) h
        · -- n >= 93345324
          rcases Nat.lt_or_ge n 93705036 with hs4 | hs4
          · -- n < 93705036
            rcases Nat.lt_or_ge n 93525180 with hs5 | hs5
            · -- n < 93525180
              exact Brocard.berndt_galway_chunk_0520 n m (by omega) (by omega) h
            · -- n >= 93525180
              exact Brocard.berndt_galway_chunk_0521 n m (by omega) (by omega) h
          · -- n >= 93705036
            exact Brocard.berndt_galway_chunk_0522 n m (by omega) (by omega) h
    · -- n >= 93884892
      rcases Nat.lt_or_ge n 94964029 with hs2 | hs2
      · -- n < 94964029
        rcases Nat.lt_or_ge n 94424460 with hs3 | hs3
        · -- n < 94424460
          rcases Nat.lt_or_ge n 94244604 with hs4 | hs4
          · -- n < 94244604
            rcases Nat.lt_or_ge n 94064748 with hs5 | hs5
            · -- n < 94064748
              exact Brocard.berndt_galway_chunk_0523 n m (by omega) (by omega) h
            · -- n >= 94064748
              exact Brocard.berndt_galway_chunk_0524 n m (by omega) (by omega) h
          · -- n >= 94244604
            exact Brocard.berndt_galway_chunk_0525 n m (by omega) (by omega) h
        · -- n >= 94424460
          rcases Nat.lt_or_ge n 94784173 with hs4 | hs4
          · -- n < 94784173
            rcases Nat.lt_or_ge n 94604316 with hs5 | hs5
            · -- n < 94604316
              exact Brocard.berndt_galway_chunk_0526 n m (by omega) (by omega) h
            · -- n >= 94604316
              exact Brocard.berndt_galway_chunk_0527 n m (by omega) (by omega) h
          · -- n >= 94784173
            exact Brocard.berndt_galway_chunk_0528 n m (by omega) (by omega) h
      · -- n >= 94964029
        rcases Nat.lt_or_ge n 95503597 with hs3 | hs3
        · -- n < 95503597
          rcases Nat.lt_or_ge n 95323741 with hs4 | hs4
          · -- n < 95323741
            rcases Nat.lt_or_ge n 95143885 with hs5 | hs5
            · -- n < 95143885
              exact Brocard.berndt_galway_chunk_0529 n m (by omega) (by omega) h
            · -- n >= 95143885
              exact Brocard.berndt_galway_chunk_0530 n m (by omega) (by omega) h
          · -- n >= 95323741
            exact Brocard.berndt_galway_chunk_0531 n m (by omega) (by omega) h
        · -- n >= 95503597
          rcases Nat.lt_or_ge n 95683453 with hs4 | hs4
          · -- n < 95683453
            exact Brocard.berndt_galway_chunk_0532 n m (by omega) (by omega) h
          · -- n >= 95683453
            exact Brocard.berndt_galway_chunk_0533 n m (by omega) (by omega) h
  · -- n >= 95863309
    rcases Nat.lt_or_ge n 98021582 with hs1 | hs1
    · -- n < 98021582
      rcases Nat.lt_or_ge n 96942446 with hs2 | hs2
      · -- n < 96942446
        rcases Nat.lt_or_ge n 96402877 with hs3 | hs3
        · -- n < 96402877
          rcases Nat.lt_or_ge n 96223021 with hs4 | hs4
          · -- n < 96223021
            rcases Nat.lt_or_ge n 96043165 with hs5 | hs5
            · -- n < 96043165
              exact Brocard.berndt_galway_chunk_0534 n m (by omega) (by omega) h
            · -- n >= 96043165
              exact Brocard.berndt_galway_chunk_0535 n m (by omega) (by omega) h
          · -- n >= 96223021
            exact Brocard.berndt_galway_chunk_0536 n m (by omega) (by omega) h
        · -- n >= 96402877
          rcases Nat.lt_or_ge n 96762590 with hs4 | hs4
          · -- n < 96762590
            rcases Nat.lt_or_ge n 96582734 with hs5 | hs5
            · -- n < 96582734
              exact Brocard.berndt_galway_chunk_0537 n m (by omega) (by omega) h
            · -- n >= 96582734
              exact Brocard.berndt_galway_chunk_0538 n m (by omega) (by omega) h
          · -- n >= 96762590
            exact Brocard.berndt_galway_chunk_0539 n m (by omega) (by omega) h
      · -- n >= 96942446
        rcases Nat.lt_or_ge n 97482014 with hs3 | hs3
        · -- n < 97482014
          rcases Nat.lt_or_ge n 97302158 with hs4 | hs4
          · -- n < 97302158
            rcases Nat.lt_or_ge n 97122302 with hs5 | hs5
            · -- n < 97122302
              exact Brocard.berndt_galway_chunk_0540 n m (by omega) (by omega) h
            · -- n >= 97122302
              exact Brocard.berndt_galway_chunk_0541 n m (by omega) (by omega) h
          · -- n >= 97302158
            exact Brocard.berndt_galway_chunk_0542 n m (by omega) (by omega) h
        · -- n >= 97482014
          rcases Nat.lt_or_ge n 97841726 with hs4 | hs4
          · -- n < 97841726
            rcases Nat.lt_or_ge n 97661870 with hs5 | hs5
            · -- n < 97661870
              exact Brocard.berndt_galway_chunk_0543 n m (by omega) (by omega) h
            · -- n >= 97661870
              exact Brocard.berndt_galway_chunk_0544 n m (by omega) (by omega) h
          · -- n >= 97841726
            exact Brocard.berndt_galway_chunk_0545 n m (by omega) (by omega) h
    · -- n >= 98021582
      rcases Nat.lt_or_ge n 99100719 with hs2 | hs2
      · -- n < 99100719
        rcases Nat.lt_or_ge n 98561151 with hs3 | hs3
        · -- n < 98561151
          rcases Nat.lt_or_ge n 98381295 with hs4 | hs4
          · -- n < 98381295
            rcases Nat.lt_or_ge n 98201438 with hs5 | hs5
            · -- n < 98201438
              exact Brocard.berndt_galway_chunk_0546 n m (by omega) (by omega) h
            · -- n >= 98201438
              exact Brocard.berndt_galway_chunk_0547 n m (by omega) (by omega) h
          · -- n >= 98381295
            exact Brocard.berndt_galway_chunk_0548 n m (by omega) (by omega) h
        · -- n >= 98561151
          rcases Nat.lt_or_ge n 98920863 with hs4 | hs4
          · -- n < 98920863
            rcases Nat.lt_or_ge n 98741007 with hs5 | hs5
            · -- n < 98741007
              exact Brocard.berndt_galway_chunk_0549 n m (by omega) (by omega) h
            · -- n >= 98741007
              exact Brocard.berndt_galway_chunk_0550 n m (by omega) (by omega) h
          · -- n >= 98920863
            exact Brocard.berndt_galway_chunk_0551 n m (by omega) (by omega) h
      · -- n >= 99100719
        rcases Nat.lt_or_ge n 99640287 with hs3 | hs3
        · -- n < 99640287
          rcases Nat.lt_or_ge n 99460431 with hs4 | hs4
          · -- n < 99460431
            rcases Nat.lt_or_ge n 99280575 with hs5 | hs5
            · -- n < 99280575
              exact Brocard.berndt_galway_chunk_0552 n m (by omega) (by omega) h
            · -- n >= 99280575
              exact Brocard.berndt_galway_chunk_0553 n m (by omega) (by omega) h
          · -- n >= 99460431
            exact Brocard.berndt_galway_chunk_0554 n m (by omega) (by omega) h
        · -- n >= 99640287
          rcases Nat.lt_or_ge n 99820143 with hs4 | hs4
          · -- n < 99820143
            exact Brocard.berndt_galway_chunk_0555 n m (by omega) (by omega) h
          · -- n >= 99820143
            exact Brocard.berndt_galway_chunk_0556 n m (by omega) (by omega) h
