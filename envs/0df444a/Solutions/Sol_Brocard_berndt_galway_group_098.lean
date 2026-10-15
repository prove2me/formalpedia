-- Prove2me | solution 1 for Brocard.berndt_galway_group_098
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:05:56.205883+00:00
-- url     : https://prove2.me/submissions/c90f6131-55d4-408a-ae8e-ea6526b2ae2a

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_4496
import Theorems.Thm_Brocard_berndt_galway_chunk_4497
import Theorems.Thm_Brocard_berndt_galway_chunk_4498
import Theorems.Thm_Brocard_berndt_galway_chunk_4499
import Theorems.Thm_Brocard_berndt_galway_chunk_4500
import Theorems.Thm_Brocard_berndt_galway_chunk_4501
import Theorems.Thm_Brocard_berndt_galway_chunk_4502
import Theorems.Thm_Brocard_berndt_galway_chunk_4503
import Theorems.Thm_Brocard_berndt_galway_chunk_4504
import Theorems.Thm_Brocard_berndt_galway_chunk_4505
import Theorems.Thm_Brocard_berndt_galway_chunk_4506
import Theorems.Thm_Brocard_berndt_galway_chunk_4507
import Theorems.Thm_Brocard_berndt_galway_chunk_4508
import Theorems.Thm_Brocard_berndt_galway_chunk_4509
import Theorems.Thm_Brocard_berndt_galway_chunk_4510
import Theorems.Thm_Brocard_berndt_galway_chunk_4511
import Theorems.Thm_Brocard_berndt_galway_chunk_4512
import Theorems.Thm_Brocard_berndt_galway_chunk_4513
import Theorems.Thm_Brocard_berndt_galway_chunk_4514
import Theorems.Thm_Brocard_berndt_galway_chunk_4515
import Theorems.Thm_Brocard_berndt_galway_chunk_4516
import Theorems.Thm_Brocard_berndt_galway_chunk_4517
import Theorems.Thm_Brocard_berndt_galway_chunk_4518
import Theorems.Thm_Brocard_berndt_galway_chunk_4519
import Theorems.Thm_Brocard_berndt_galway_chunk_4520
import Theorems.Thm_Brocard_berndt_galway_chunk_4521
import Theorems.Thm_Brocard_berndt_galway_chunk_4522
import Theorems.Thm_Brocard_berndt_galway_chunk_4523
import Theorems.Thm_Brocard_berndt_galway_chunk_4524
import Theorems.Thm_Brocard_berndt_galway_chunk_4525
import Theorems.Thm_Brocard_berndt_galway_chunk_4526
import Theorems.Thm_Brocard_berndt_galway_chunk_4527
import Theorems.Thm_Brocard_berndt_galway_chunk_4528
import Theorems.Thm_Brocard_berndt_galway_chunk_4529
import Theorems.Thm_Brocard_berndt_galway_chunk_4530
import Theorems.Thm_Brocard_berndt_galway_chunk_4531
import Theorems.Thm_Brocard_berndt_galway_chunk_4532
import Theorems.Thm_Brocard_berndt_galway_chunk_4533
import Theorems.Thm_Brocard_berndt_galway_chunk_4534
import Theorems.Thm_Brocard_berndt_galway_chunk_4535
import Theorems.Thm_Brocard_berndt_galway_chunk_4536
import Theorems.Thm_Brocard_berndt_galway_chunk_4537
import Theorems.Thm_Brocard_berndt_galway_chunk_4538
import Theorems.Thm_Brocard_berndt_galway_chunk_4539
import Theorems.Thm_Brocard_berndt_galway_chunk_4540
import Theorems.Thm_Brocard_berndt_galway_chunk_4541
import Theorems.Thm_Brocard_berndt_galway_chunk_4542

theorem solution (n m : ℕ) (h1 : 808453237 ≤ n) (h2 : n < 816906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 812769784 with hs0 | hs0
  · -- n < 812769784
    rcases Nat.lt_or_ge n 810611510 with hs1 | hs1
    · -- n < 810611510
      rcases Nat.lt_or_ge n 809532374 with hs2 | hs2
      · -- n < 809532374
        rcases Nat.lt_or_ge n 808992805 with hs3 | hs3
        · -- n < 808992805
          rcases Nat.lt_or_ge n 808812949 with hs4 | hs4
          · -- n < 808812949
            rcases Nat.lt_or_ge n 808633093 with hs5 | hs5
            · -- n < 808633093
              exact Brocard.berndt_galway_chunk_4496 n m (by omega) (by omega) h
            · -- n >= 808633093
              exact Brocard.berndt_galway_chunk_4497 n m (by omega) (by omega) h
          · -- n >= 808812949
            exact Brocard.berndt_galway_chunk_4498 n m (by omega) (by omega) h
        · -- n >= 808992805
          rcases Nat.lt_or_ge n 809352517 with hs4 | hs4
          · -- n < 809352517
            rcases Nat.lt_or_ge n 809172661 with hs5 | hs5
            · -- n < 809172661
              exact Brocard.berndt_galway_chunk_4499 n m (by omega) (by omega) h
            · -- n >= 809172661
              exact Brocard.berndt_galway_chunk_4500 n m (by omega) (by omega) h
          · -- n >= 809352517
            exact Brocard.berndt_galway_chunk_4501 n m (by omega) (by omega) h
      · -- n >= 809532374
        rcases Nat.lt_or_ge n 810071942 with hs3 | hs3
        · -- n < 810071942
          rcases Nat.lt_or_ge n 809892086 with hs4 | hs4
          · -- n < 809892086
            rcases Nat.lt_or_ge n 809712230 with hs5 | hs5
            · -- n < 809712230
              exact Brocard.berndt_galway_chunk_4502 n m (by omega) (by omega) h
            · -- n >= 809712230
              exact Brocard.berndt_galway_chunk_4503 n m (by omega) (by omega) h
          · -- n >= 809892086
            exact Brocard.berndt_galway_chunk_4504 n m (by omega) (by omega) h
        · -- n >= 810071942
          rcases Nat.lt_or_ge n 810431654 with hs4 | hs4
          · -- n < 810431654
            rcases Nat.lt_or_ge n 810251798 with hs5 | hs5
            · -- n < 810251798
              exact Brocard.berndt_galway_chunk_4505 n m (by omega) (by omega) h
            · -- n >= 810251798
              exact Brocard.berndt_galway_chunk_4506 n m (by omega) (by omega) h
          · -- n >= 810431654
            exact Brocard.berndt_galway_chunk_4507 n m (by omega) (by omega) h
    · -- n >= 810611510
      rcases Nat.lt_or_ge n 811690647 with hs2 | hs2
      · -- n < 811690647
        rcases Nat.lt_or_ge n 811151079 with hs3 | hs3
        · -- n < 811151079
          rcases Nat.lt_or_ge n 810971223 with hs4 | hs4
          · -- n < 810971223
            rcases Nat.lt_or_ge n 810791366 with hs5 | hs5
            · -- n < 810791366
              exact Brocard.berndt_galway_chunk_4508 n m (by omega) (by omega) h
            · -- n >= 810791366
              exact Brocard.berndt_galway_chunk_4509 n m (by omega) (by omega) h
          · -- n >= 810971223
            exact Brocard.berndt_galway_chunk_4510 n m (by omega) (by omega) h
        · -- n >= 811151079
          rcases Nat.lt_or_ge n 811510791 with hs4 | hs4
          · -- n < 811510791
            rcases Nat.lt_or_ge n 811330935 with hs5 | hs5
            · -- n < 811330935
              exact Brocard.berndt_galway_chunk_4511 n m (by omega) (by omega) h
            · -- n >= 811330935
              exact Brocard.berndt_galway_chunk_4512 n m (by omega) (by omega) h
          · -- n >= 811510791
            exact Brocard.berndt_galway_chunk_4513 n m (by omega) (by omega) h
      · -- n >= 811690647
        rcases Nat.lt_or_ge n 812230215 with hs3 | hs3
        · -- n < 812230215
          rcases Nat.lt_or_ge n 812050359 with hs4 | hs4
          · -- n < 812050359
            rcases Nat.lt_or_ge n 811870503 with hs5 | hs5
            · -- n < 811870503
              exact Brocard.berndt_galway_chunk_4514 n m (by omega) (by omega) h
            · -- n >= 811870503
              exact Brocard.berndt_galway_chunk_4515 n m (by omega) (by omega) h
          · -- n >= 812050359
            exact Brocard.berndt_galway_chunk_4516 n m (by omega) (by omega) h
        · -- n >= 812230215
          rcases Nat.lt_or_ge n 812589928 with hs4 | hs4
          · -- n < 812589928
            rcases Nat.lt_or_ge n 812410071 with hs5 | hs5
            · -- n < 812410071
              exact Brocard.berndt_galway_chunk_4517 n m (by omega) (by omega) h
            · -- n >= 812410071
              exact Brocard.berndt_galway_chunk_4518 n m (by omega) (by omega) h
          · -- n >= 812589928
            exact Brocard.berndt_galway_chunk_4519 n m (by omega) (by omega) h
  · -- n >= 812769784
    rcases Nat.lt_or_ge n 814928057 with hs1 | hs1
    · -- n < 814928057
      rcases Nat.lt_or_ge n 813848920 with hs2 | hs2
      · -- n < 813848920
        rcases Nat.lt_or_ge n 813309352 with hs3 | hs3
        · -- n < 813309352
          rcases Nat.lt_or_ge n 813129496 with hs4 | hs4
          · -- n < 813129496
            rcases Nat.lt_or_ge n 812949640 with hs5 | hs5
            · -- n < 812949640
              exact Brocard.berndt_galway_chunk_4520 n m (by omega) (by omega) h
            · -- n >= 812949640
              exact Brocard.berndt_galway_chunk_4521 n m (by omega) (by omega) h
          · -- n >= 813129496
            exact Brocard.berndt_galway_chunk_4522 n m (by omega) (by omega) h
        · -- n >= 813309352
          rcases Nat.lt_or_ge n 813669064 with hs4 | hs4
          · -- n < 813669064
            rcases Nat.lt_or_ge n 813489208 with hs5 | hs5
            · -- n < 813489208
              exact Brocard.berndt_galway_chunk_4523 n m (by omega) (by omega) h
            · -- n >= 813489208
              exact Brocard.berndt_galway_chunk_4524 n m (by omega) (by omega) h
          · -- n >= 813669064
            exact Brocard.berndt_galway_chunk_4525 n m (by omega) (by omega) h
      · -- n >= 813848920
        rcases Nat.lt_or_ge n 814388489 with hs3 | hs3
        · -- n < 814388489
          rcases Nat.lt_or_ge n 814208633 with hs4 | hs4
          · -- n < 814208633
            rcases Nat.lt_or_ge n 814028776 with hs5 | hs5
            · -- n < 814028776
              exact Brocard.berndt_galway_chunk_4526 n m (by omega) (by omega) h
            · -- n >= 814028776
              exact Brocard.berndt_galway_chunk_4527 n m (by omega) (by omega) h
          · -- n >= 814208633
            exact Brocard.berndt_galway_chunk_4528 n m (by omega) (by omega) h
        · -- n >= 814388489
          rcases Nat.lt_or_ge n 814748201 with hs4 | hs4
          · -- n < 814748201
            rcases Nat.lt_or_ge n 814568345 with hs5 | hs5
            · -- n < 814568345
              exact Brocard.berndt_galway_chunk_4529 n m (by omega) (by omega) h
            · -- n >= 814568345
              exact Brocard.berndt_galway_chunk_4530 n m (by omega) (by omega) h
          · -- n >= 814748201
            exact Brocard.berndt_galway_chunk_4531 n m (by omega) (by omega) h
    · -- n >= 814928057
      rcases Nat.lt_or_ge n 816007194 with hs2 | hs2
      · -- n < 816007194
        rcases Nat.lt_or_ge n 815467625 with hs3 | hs3
        · -- n < 815467625
          rcases Nat.lt_or_ge n 815287769 with hs4 | hs4
          · -- n < 815287769
            rcases Nat.lt_or_ge n 815107913 with hs5 | hs5
            · -- n < 815107913
              exact Brocard.berndt_galway_chunk_4532 n m (by omega) (by omega) h
            · -- n >= 815107913
              exact Brocard.berndt_galway_chunk_4533 n m (by omega) (by omega) h
          · -- n >= 815287769
            exact Brocard.berndt_galway_chunk_4534 n m (by omega) (by omega) h
        · -- n >= 815467625
          rcases Nat.lt_or_ge n 815827338 with hs4 | hs4
          · -- n < 815827338
            rcases Nat.lt_or_ge n 815647482 with hs5 | hs5
            · -- n < 815647482
              exact Brocard.berndt_galway_chunk_4535 n m (by omega) (by omega) h
            · -- n >= 815647482
              exact Brocard.berndt_galway_chunk_4536 n m (by omega) (by omega) h
          · -- n >= 815827338
            exact Brocard.berndt_galway_chunk_4537 n m (by omega) (by omega) h
      · -- n >= 816007194
        rcases Nat.lt_or_ge n 816546762 with hs3 | hs3
        · -- n < 816546762
          rcases Nat.lt_or_ge n 816366906 with hs4 | hs4
          · -- n < 816366906
            rcases Nat.lt_or_ge n 816187050 with hs5 | hs5
            · -- n < 816187050
              exact Brocard.berndt_galway_chunk_4538 n m (by omega) (by omega) h
            · -- n >= 816187050
              exact Brocard.berndt_galway_chunk_4539 n m (by omega) (by omega) h
          · -- n >= 816366906
            exact Brocard.berndt_galway_chunk_4540 n m (by omega) (by omega) h
        · -- n >= 816546762
          rcases Nat.lt_or_ge n 816726618 with hs4 | hs4
          · -- n < 816726618
            exact Brocard.berndt_galway_chunk_4541 n m (by omega) (by omega) h
          · -- n >= 816726618
            exact Brocard.berndt_galway_chunk_4542 n m (by omega) (by omega) h
