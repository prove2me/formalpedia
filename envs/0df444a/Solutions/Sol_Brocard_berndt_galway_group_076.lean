-- Prove2me | solution 1 for Brocard.berndt_galway_group_076
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:03:36.342835+00:00
-- url     : https://prove2.me/submissions/bab2e592-656f-4142-8bfd-4e59ac5d241a

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_3478
import Theorems.Thm_Brocard_berndt_galway_chunk_3479
import Theorems.Thm_Brocard_berndt_galway_chunk_3480
import Theorems.Thm_Brocard_berndt_galway_chunk_3481
import Theorems.Thm_Brocard_berndt_galway_chunk_3482
import Theorems.Thm_Brocard_berndt_galway_chunk_3483
import Theorems.Thm_Brocard_berndt_galway_chunk_3484
import Theorems.Thm_Brocard_berndt_galway_chunk_3485
import Theorems.Thm_Brocard_berndt_galway_chunk_3486
import Theorems.Thm_Brocard_berndt_galway_chunk_3487
import Theorems.Thm_Brocard_berndt_galway_chunk_3488
import Theorems.Thm_Brocard_berndt_galway_chunk_3489
import Theorems.Thm_Brocard_berndt_galway_chunk_3490
import Theorems.Thm_Brocard_berndt_galway_chunk_3491
import Theorems.Thm_Brocard_berndt_galway_chunk_3492
import Theorems.Thm_Brocard_berndt_galway_chunk_3493
import Theorems.Thm_Brocard_berndt_galway_chunk_3494
import Theorems.Thm_Brocard_berndt_galway_chunk_3495
import Theorems.Thm_Brocard_berndt_galway_chunk_3496
import Theorems.Thm_Brocard_berndt_galway_chunk_3497
import Theorems.Thm_Brocard_berndt_galway_chunk_3498
import Theorems.Thm_Brocard_berndt_galway_chunk_3499
import Theorems.Thm_Brocard_berndt_galway_chunk_3500
import Theorems.Thm_Brocard_berndt_galway_chunk_3501
import Theorems.Thm_Brocard_berndt_galway_chunk_3502
import Theorems.Thm_Brocard_berndt_galway_chunk_3503
import Theorems.Thm_Brocard_berndt_galway_chunk_3504
import Theorems.Thm_Brocard_berndt_galway_chunk_3505
import Theorems.Thm_Brocard_berndt_galway_chunk_3506
import Theorems.Thm_Brocard_berndt_galway_chunk_3507
import Theorems.Thm_Brocard_berndt_galway_chunk_3508
import Theorems.Thm_Brocard_berndt_galway_chunk_3509
import Theorems.Thm_Brocard_berndt_galway_chunk_3510
import Theorems.Thm_Brocard_berndt_galway_chunk_3511
import Theorems.Thm_Brocard_berndt_galway_chunk_3512
import Theorems.Thm_Brocard_berndt_galway_chunk_3513
import Theorems.Thm_Brocard_berndt_galway_chunk_3514
import Theorems.Thm_Brocard_berndt_galway_chunk_3515
import Theorems.Thm_Brocard_berndt_galway_chunk_3516
import Theorems.Thm_Brocard_berndt_galway_chunk_3517
import Theorems.Thm_Brocard_berndt_galway_chunk_3518
import Theorems.Thm_Brocard_berndt_galway_chunk_3519
import Theorems.Thm_Brocard_berndt_galway_chunk_3520
import Theorems.Thm_Brocard_berndt_galway_chunk_3521
import Theorems.Thm_Brocard_berndt_galway_chunk_3522
import Theorems.Thm_Brocard_berndt_galway_chunk_3523
import Theorems.Thm_Brocard_berndt_galway_chunk_3524

theorem solution (n m : ℕ) (h1 : 625359712 ≤ n) (h2 : n < 633812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 629676258 with hs0 | hs0
  · -- n < 629676258
    rcases Nat.lt_or_ge n 627517985 with hs1 | hs1
    · -- n < 627517985
      rcases Nat.lt_or_ge n 626438848 with hs2 | hs2
      · -- n < 626438848
        rcases Nat.lt_or_ge n 625899280 with hs3 | hs3
        · -- n < 625899280
          rcases Nat.lt_or_ge n 625719424 with hs4 | hs4
          · -- n < 625719424
            rcases Nat.lt_or_ge n 625539568 with hs5 | hs5
            · -- n < 625539568
              exact Brocard.berndt_galway_chunk_3478 n m (by omega) (by omega) h
            · -- n >= 625539568
              exact Brocard.berndt_galway_chunk_3479 n m (by omega) (by omega) h
          · -- n >= 625719424
            exact Brocard.berndt_galway_chunk_3480 n m (by omega) (by omega) h
        · -- n >= 625899280
          rcases Nat.lt_or_ge n 626258992 with hs4 | hs4
          · -- n < 626258992
            rcases Nat.lt_or_ge n 626079136 with hs5 | hs5
            · -- n < 626079136
              exact Brocard.berndt_galway_chunk_3481 n m (by omega) (by omega) h
            · -- n >= 626079136
              exact Brocard.berndt_galway_chunk_3482 n m (by omega) (by omega) h
          · -- n >= 626258992
            exact Brocard.berndt_galway_chunk_3483 n m (by omega) (by omega) h
      · -- n >= 626438848
        rcases Nat.lt_or_ge n 626978417 with hs3 | hs3
        · -- n < 626978417
          rcases Nat.lt_or_ge n 626798561 with hs4 | hs4
          · -- n < 626798561
            rcases Nat.lt_or_ge n 626618705 with hs5 | hs5
            · -- n < 626618705
              exact Brocard.berndt_galway_chunk_3484 n m (by omega) (by omega) h
            · -- n >= 626618705
              exact Brocard.berndt_galway_chunk_3485 n m (by omega) (by omega) h
          · -- n >= 626798561
            exact Brocard.berndt_galway_chunk_3486 n m (by omega) (by omega) h
        · -- n >= 626978417
          rcases Nat.lt_or_ge n 627338129 with hs4 | hs4
          · -- n < 627338129
            rcases Nat.lt_or_ge n 627158273 with hs5 | hs5
            · -- n < 627158273
              exact Brocard.berndt_galway_chunk_3487 n m (by omega) (by omega) h
            · -- n >= 627158273
              exact Brocard.berndt_galway_chunk_3488 n m (by omega) (by omega) h
          · -- n >= 627338129
            exact Brocard.berndt_galway_chunk_3489 n m (by omega) (by omega) h
    · -- n >= 627517985
      rcases Nat.lt_or_ge n 628597122 with hs2 | hs2
      · -- n < 628597122
        rcases Nat.lt_or_ge n 628057553 with hs3 | hs3
        · -- n < 628057553
          rcases Nat.lt_or_ge n 627877697 with hs4 | hs4
          · -- n < 627877697
            rcases Nat.lt_or_ge n 627697841 with hs5 | hs5
            · -- n < 627697841
              exact Brocard.berndt_galway_chunk_3490 n m (by omega) (by omega) h
            · -- n >= 627697841
              exact Brocard.berndt_galway_chunk_3491 n m (by omega) (by omega) h
          · -- n >= 627877697
            exact Brocard.berndt_galway_chunk_3492 n m (by omega) (by omega) h
        · -- n >= 628057553
          rcases Nat.lt_or_ge n 628417266 with hs4 | hs4
          · -- n < 628417266
            rcases Nat.lt_or_ge n 628237410 with hs5 | hs5
            · -- n < 628237410
              exact Brocard.berndt_galway_chunk_3493 n m (by omega) (by omega) h
            · -- n >= 628237410
              exact Brocard.berndt_galway_chunk_3494 n m (by omega) (by omega) h
          · -- n >= 628417266
            exact Brocard.berndt_galway_chunk_3495 n m (by omega) (by omega) h
      · -- n >= 628597122
        rcases Nat.lt_or_ge n 629136690 with hs3 | hs3
        · -- n < 629136690
          rcases Nat.lt_or_ge n 628956834 with hs4 | hs4
          · -- n < 628956834
            rcases Nat.lt_or_ge n 628776978 with hs5 | hs5
            · -- n < 628776978
              exact Brocard.berndt_galway_chunk_3496 n m (by omega) (by omega) h
            · -- n >= 628776978
              exact Brocard.berndt_galway_chunk_3497 n m (by omega) (by omega) h
          · -- n >= 628956834
            exact Brocard.berndt_galway_chunk_3498 n m (by omega) (by omega) h
        · -- n >= 629136690
          rcases Nat.lt_or_ge n 629496402 with hs4 | hs4
          · -- n < 629496402
            rcases Nat.lt_or_ge n 629316546 with hs5 | hs5
            · -- n < 629316546
              exact Brocard.berndt_galway_chunk_3499 n m (by omega) (by omega) h
            · -- n >= 629316546
              exact Brocard.berndt_galway_chunk_3500 n m (by omega) (by omega) h
          · -- n >= 629496402
            exact Brocard.berndt_galway_chunk_3501 n m (by omega) (by omega) h
  · -- n >= 629676258
    rcases Nat.lt_or_ge n 631834532 with hs1 | hs1
    · -- n < 631834532
      rcases Nat.lt_or_ge n 630755395 with hs2 | hs2
      · -- n < 630755395
        rcases Nat.lt_or_ge n 630215827 with hs3 | hs3
        · -- n < 630215827
          rcases Nat.lt_or_ge n 630035971 with hs4 | hs4
          · -- n < 630035971
            rcases Nat.lt_or_ge n 629856115 with hs5 | hs5
            · -- n < 629856115
              exact Brocard.berndt_galway_chunk_3502 n m (by omega) (by omega) h
            · -- n >= 629856115
              exact Brocard.berndt_galway_chunk_3503 n m (by omega) (by omega) h
          · -- n >= 630035971
            exact Brocard.berndt_galway_chunk_3504 n m (by omega) (by omega) h
        · -- n >= 630215827
          rcases Nat.lt_or_ge n 630575539 with hs4 | hs4
          · -- n < 630575539
            rcases Nat.lt_or_ge n 630395683 with hs5 | hs5
            · -- n < 630395683
              exact Brocard.berndt_galway_chunk_3505 n m (by omega) (by omega) h
            · -- n >= 630395683
              exact Brocard.berndt_galway_chunk_3506 n m (by omega) (by omega) h
          · -- n >= 630575539
            exact Brocard.berndt_galway_chunk_3507 n m (by omega) (by omega) h
      · -- n >= 630755395
        rcases Nat.lt_or_ge n 631294964 with hs3 | hs3
        · -- n < 631294964
          rcases Nat.lt_or_ge n 631115107 with hs4 | hs4
          · -- n < 631115107
            rcases Nat.lt_or_ge n 630935251 with hs5 | hs5
            · -- n < 630935251
              exact Brocard.berndt_galway_chunk_3508 n m (by omega) (by omega) h
            · -- n >= 630935251
              exact Brocard.berndt_galway_chunk_3509 n m (by omega) (by omega) h
          · -- n >= 631115107
            exact Brocard.berndt_galway_chunk_3510 n m (by omega) (by omega) h
        · -- n >= 631294964
          rcases Nat.lt_or_ge n 631654676 with hs4 | hs4
          · -- n < 631654676
            rcases Nat.lt_or_ge n 631474820 with hs5 | hs5
            · -- n < 631474820
              exact Brocard.berndt_galway_chunk_3511 n m (by omega) (by omega) h
            · -- n >= 631474820
              exact Brocard.berndt_galway_chunk_3512 n m (by omega) (by omega) h
          · -- n >= 631654676
            exact Brocard.berndt_galway_chunk_3513 n m (by omega) (by omega) h
    · -- n >= 631834532
      rcases Nat.lt_or_ge n 632913669 with hs2 | hs2
      · -- n < 632913669
        rcases Nat.lt_or_ge n 632374100 with hs3 | hs3
        · -- n < 632374100
          rcases Nat.lt_or_ge n 632194244 with hs4 | hs4
          · -- n < 632194244
            rcases Nat.lt_or_ge n 632014388 with hs5 | hs5
            · -- n < 632014388
              exact Brocard.berndt_galway_chunk_3514 n m (by omega) (by omega) h
            · -- n >= 632014388
              exact Brocard.berndt_galway_chunk_3515 n m (by omega) (by omega) h
          · -- n >= 632194244
            exact Brocard.berndt_galway_chunk_3516 n m (by omega) (by omega) h
        · -- n >= 632374100
          rcases Nat.lt_or_ge n 632733812 with hs4 | hs4
          · -- n < 632733812
            rcases Nat.lt_or_ge n 632553956 with hs5 | hs5
            · -- n < 632553956
              exact Brocard.berndt_galway_chunk_3517 n m (by omega) (by omega) h
            · -- n >= 632553956
              exact Brocard.berndt_galway_chunk_3518 n m (by omega) (by omega) h
          · -- n >= 632733812
            exact Brocard.berndt_galway_chunk_3519 n m (by omega) (by omega) h
      · -- n >= 632913669
        rcases Nat.lt_or_ge n 633453237 with hs3 | hs3
        · -- n < 633453237
          rcases Nat.lt_or_ge n 633273381 with hs4 | hs4
          · -- n < 633273381
            rcases Nat.lt_or_ge n 633093525 with hs5 | hs5
            · -- n < 633093525
              exact Brocard.berndt_galway_chunk_3520 n m (by omega) (by omega) h
            · -- n >= 633093525
              exact Brocard.berndt_galway_chunk_3521 n m (by omega) (by omega) h
          · -- n >= 633273381
            exact Brocard.berndt_galway_chunk_3522 n m (by omega) (by omega) h
        · -- n >= 633453237
          rcases Nat.lt_or_ge n 633633093 with hs4 | hs4
          · -- n < 633633093
            exact Brocard.berndt_galway_chunk_3523 n m (by omega) (by omega) h
          · -- n >= 633633093
            exact Brocard.berndt_galway_chunk_3524 n m (by omega) (by omega) h
