-- Prove2me | solution 1 for Brocard.berndt_galway_group_097
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:55:23.053702+00:00
-- url     : https://prove2.me/submissions/e01035ef-d6f4-4447-97f8-9e4e4af7d385

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_4449
import Theorems.Thm_Brocard_berndt_galway_chunk_4450
import Theorems.Thm_Brocard_berndt_galway_chunk_4451
import Theorems.Thm_Brocard_berndt_galway_chunk_4452
import Theorems.Thm_Brocard_berndt_galway_chunk_4453
import Theorems.Thm_Brocard_berndt_galway_chunk_4454
import Theorems.Thm_Brocard_berndt_galway_chunk_4455
import Theorems.Thm_Brocard_berndt_galway_chunk_4456
import Theorems.Thm_Brocard_berndt_galway_chunk_4457
import Theorems.Thm_Brocard_berndt_galway_chunk_4458
import Theorems.Thm_Brocard_berndt_galway_chunk_4459
import Theorems.Thm_Brocard_berndt_galway_chunk_4460
import Theorems.Thm_Brocard_berndt_galway_chunk_4461
import Theorems.Thm_Brocard_berndt_galway_chunk_4462
import Theorems.Thm_Brocard_berndt_galway_chunk_4463
import Theorems.Thm_Brocard_berndt_galway_chunk_4464
import Theorems.Thm_Brocard_berndt_galway_chunk_4465
import Theorems.Thm_Brocard_berndt_galway_chunk_4466
import Theorems.Thm_Brocard_berndt_galway_chunk_4467
import Theorems.Thm_Brocard_berndt_galway_chunk_4468
import Theorems.Thm_Brocard_berndt_galway_chunk_4469
import Theorems.Thm_Brocard_berndt_galway_chunk_4470
import Theorems.Thm_Brocard_berndt_galway_chunk_4471
import Theorems.Thm_Brocard_berndt_galway_chunk_4472
import Theorems.Thm_Brocard_berndt_galway_chunk_4473
import Theorems.Thm_Brocard_berndt_galway_chunk_4474
import Theorems.Thm_Brocard_berndt_galway_chunk_4475
import Theorems.Thm_Brocard_berndt_galway_chunk_4476
import Theorems.Thm_Brocard_berndt_galway_chunk_4477
import Theorems.Thm_Brocard_berndt_galway_chunk_4478
import Theorems.Thm_Brocard_berndt_galway_chunk_4479
import Theorems.Thm_Brocard_berndt_galway_chunk_4480
import Theorems.Thm_Brocard_berndt_galway_chunk_4481
import Theorems.Thm_Brocard_berndt_galway_chunk_4482
import Theorems.Thm_Brocard_berndt_galway_chunk_4483
import Theorems.Thm_Brocard_berndt_galway_chunk_4484
import Theorems.Thm_Brocard_berndt_galway_chunk_4485
import Theorems.Thm_Brocard_berndt_galway_chunk_4486
import Theorems.Thm_Brocard_berndt_galway_chunk_4487
import Theorems.Thm_Brocard_berndt_galway_chunk_4488
import Theorems.Thm_Brocard_berndt_galway_chunk_4489
import Theorems.Thm_Brocard_berndt_galway_chunk_4490
import Theorems.Thm_Brocard_berndt_galway_chunk_4491
import Theorems.Thm_Brocard_berndt_galway_chunk_4492
import Theorems.Thm_Brocard_berndt_galway_chunk_4493
import Theorems.Thm_Brocard_berndt_galway_chunk_4494
import Theorems.Thm_Brocard_berndt_galway_chunk_4495

theorem solution (n m : ℕ) (h1 : 800000000 ≤ n) (h2 : n < 808453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 804316546 with hs0 | hs0
  · -- n < 804316546
    rcases Nat.lt_or_ge n 802158273 with hs1 | hs1
    · -- n < 802158273
      rcases Nat.lt_or_ge n 801079136 with hs2 | hs2
      · -- n < 801079136
        rcases Nat.lt_or_ge n 800539568 with hs3 | hs3
        · -- n < 800539568
          rcases Nat.lt_or_ge n 800359712 with hs4 | hs4
          · -- n < 800359712
            rcases Nat.lt_or_ge n 800179856 with hs5 | hs5
            · -- n < 800179856
              exact Brocard.berndt_galway_chunk_4449 n m (by omega) (by omega) h
            · -- n >= 800179856
              exact Brocard.berndt_galway_chunk_4450 n m (by omega) (by omega) h
          · -- n >= 800359712
            exact Brocard.berndt_galway_chunk_4451 n m (by omega) (by omega) h
        · -- n >= 800539568
          rcases Nat.lt_or_ge n 800899280 with hs4 | hs4
          · -- n < 800899280
            rcases Nat.lt_or_ge n 800719424 with hs5 | hs5
            · -- n < 800719424
              exact Brocard.berndt_galway_chunk_4452 n m (by omega) (by omega) h
            · -- n >= 800719424
              exact Brocard.berndt_galway_chunk_4453 n m (by omega) (by omega) h
          · -- n >= 800899280
            exact Brocard.berndt_galway_chunk_4454 n m (by omega) (by omega) h
      · -- n >= 801079136
        rcases Nat.lt_or_ge n 801618705 with hs3 | hs3
        · -- n < 801618705
          rcases Nat.lt_or_ge n 801438848 with hs4 | hs4
          · -- n < 801438848
            rcases Nat.lt_or_ge n 801258992 with hs5 | hs5
            · -- n < 801258992
              exact Brocard.berndt_galway_chunk_4455 n m (by omega) (by omega) h
            · -- n >= 801258992
              exact Brocard.berndt_galway_chunk_4456 n m (by omega) (by omega) h
          · -- n >= 801438848
            exact Brocard.berndt_galway_chunk_4457 n m (by omega) (by omega) h
        · -- n >= 801618705
          rcases Nat.lt_or_ge n 801978417 with hs4 | hs4
          · -- n < 801978417
            rcases Nat.lt_or_ge n 801798561 with hs5 | hs5
            · -- n < 801798561
              exact Brocard.berndt_galway_chunk_4458 n m (by omega) (by omega) h
            · -- n >= 801798561
              exact Brocard.berndt_galway_chunk_4459 n m (by omega) (by omega) h
          · -- n >= 801978417
            exact Brocard.berndt_galway_chunk_4460 n m (by omega) (by omega) h
    · -- n >= 802158273
      rcases Nat.lt_or_ge n 803237410 with hs2 | hs2
      · -- n < 803237410
        rcases Nat.lt_or_ge n 802697841 with hs3 | hs3
        · -- n < 802697841
          rcases Nat.lt_or_ge n 802517985 with hs4 | hs4
          · -- n < 802517985
            rcases Nat.lt_or_ge n 802338129 with hs5 | hs5
            · -- n < 802338129
              exact Brocard.berndt_galway_chunk_4461 n m (by omega) (by omega) h
            · -- n >= 802338129
              exact Brocard.berndt_galway_chunk_4462 n m (by omega) (by omega) h
          · -- n >= 802517985
            exact Brocard.berndt_galway_chunk_4463 n m (by omega) (by omega) h
        · -- n >= 802697841
          rcases Nat.lt_or_ge n 803057553 with hs4 | hs4
          · -- n < 803057553
            rcases Nat.lt_or_ge n 802877697 with hs5 | hs5
            · -- n < 802877697
              exact Brocard.berndt_galway_chunk_4464 n m (by omega) (by omega) h
            · -- n >= 802877697
              exact Brocard.berndt_galway_chunk_4465 n m (by omega) (by omega) h
          · -- n >= 803057553
            exact Brocard.berndt_galway_chunk_4466 n m (by omega) (by omega) h
      · -- n >= 803237410
        rcases Nat.lt_or_ge n 803776978 with hs3 | hs3
        · -- n < 803776978
          rcases Nat.lt_or_ge n 803597122 with hs4 | hs4
          · -- n < 803597122
            rcases Nat.lt_or_ge n 803417266 with hs5 | hs5
            · -- n < 803417266
              exact Brocard.berndt_galway_chunk_4467 n m (by omega) (by omega) h
            · -- n >= 803417266
              exact Brocard.berndt_galway_chunk_4468 n m (by omega) (by omega) h
          · -- n >= 803597122
            exact Brocard.berndt_galway_chunk_4469 n m (by omega) (by omega) h
        · -- n >= 803776978
          rcases Nat.lt_or_ge n 804136690 with hs4 | hs4
          · -- n < 804136690
            rcases Nat.lt_or_ge n 803956834 with hs5 | hs5
            · -- n < 803956834
              exact Brocard.berndt_galway_chunk_4470 n m (by omega) (by omega) h
            · -- n >= 803956834
              exact Brocard.berndt_galway_chunk_4471 n m (by omega) (by omega) h
          · -- n >= 804136690
            exact Brocard.berndt_galway_chunk_4472 n m (by omega) (by omega) h
  · -- n >= 804316546
    rcases Nat.lt_or_ge n 806474820 with hs1 | hs1
    · -- n < 806474820
      rcases Nat.lt_or_ge n 805395683 with hs2 | hs2
      · -- n < 805395683
        rcases Nat.lt_or_ge n 804856115 with hs3 | hs3
        · -- n < 804856115
          rcases Nat.lt_or_ge n 804676258 with hs4 | hs4
          · -- n < 804676258
            rcases Nat.lt_or_ge n 804496402 with hs5 | hs5
            · -- n < 804496402
              exact Brocard.berndt_galway_chunk_4473 n m (by omega) (by omega) h
            · -- n >= 804496402
              exact Brocard.berndt_galway_chunk_4474 n m (by omega) (by omega) h
          · -- n >= 804676258
            exact Brocard.berndt_galway_chunk_4475 n m (by omega) (by omega) h
        · -- n >= 804856115
          rcases Nat.lt_or_ge n 805215827 with hs4 | hs4
          · -- n < 805215827
            rcases Nat.lt_or_ge n 805035971 with hs5 | hs5
            · -- n < 805035971
              exact Brocard.berndt_galway_chunk_4476 n m (by omega) (by omega) h
            · -- n >= 805035971
              exact Brocard.berndt_galway_chunk_4477 n m (by omega) (by omega) h
          · -- n >= 805215827
            exact Brocard.berndt_galway_chunk_4478 n m (by omega) (by omega) h
      · -- n >= 805395683
        rcases Nat.lt_or_ge n 805935251 with hs3 | hs3
        · -- n < 805935251
          rcases Nat.lt_or_ge n 805755395 with hs4 | hs4
          · -- n < 805755395
            rcases Nat.lt_or_ge n 805575539 with hs5 | hs5
            · -- n < 805575539
              exact Brocard.berndt_galway_chunk_4479 n m (by omega) (by omega) h
            · -- n >= 805575539
              exact Brocard.berndt_galway_chunk_4480 n m (by omega) (by omega) h
          · -- n >= 805755395
            exact Brocard.berndt_galway_chunk_4481 n m (by omega) (by omega) h
        · -- n >= 805935251
          rcases Nat.lt_or_ge n 806294964 with hs4 | hs4
          · -- n < 806294964
            rcases Nat.lt_or_ge n 806115107 with hs5 | hs5
            · -- n < 806115107
              exact Brocard.berndt_galway_chunk_4482 n m (by omega) (by omega) h
            · -- n >= 806115107
              exact Brocard.berndt_galway_chunk_4483 n m (by omega) (by omega) h
          · -- n >= 806294964
            exact Brocard.berndt_galway_chunk_4484 n m (by omega) (by omega) h
    · -- n >= 806474820
      rcases Nat.lt_or_ge n 807553956 with hs2 | hs2
      · -- n < 807553956
        rcases Nat.lt_or_ge n 807014388 with hs3 | hs3
        · -- n < 807014388
          rcases Nat.lt_or_ge n 806834532 with hs4 | hs4
          · -- n < 806834532
            rcases Nat.lt_or_ge n 806654676 with hs5 | hs5
            · -- n < 806654676
              exact Brocard.berndt_galway_chunk_4485 n m (by omega) (by omega) h
            · -- n >= 806654676
              exact Brocard.berndt_galway_chunk_4486 n m (by omega) (by omega) h
          · -- n >= 806834532
            exact Brocard.berndt_galway_chunk_4487 n m (by omega) (by omega) h
        · -- n >= 807014388
          rcases Nat.lt_or_ge n 807374100 with hs4 | hs4
          · -- n < 807374100
            rcases Nat.lt_or_ge n 807194244 with hs5 | hs5
            · -- n < 807194244
              exact Brocard.berndt_galway_chunk_4488 n m (by omega) (by omega) h
            · -- n >= 807194244
              exact Brocard.berndt_galway_chunk_4489 n m (by omega) (by omega) h
          · -- n >= 807374100
            exact Brocard.berndt_galway_chunk_4490 n m (by omega) (by omega) h
      · -- n >= 807553956
        rcases Nat.lt_or_ge n 808093525 with hs3 | hs3
        · -- n < 808093525
          rcases Nat.lt_or_ge n 807913669 with hs4 | hs4
          · -- n < 807913669
            rcases Nat.lt_or_ge n 807733812 with hs5 | hs5
            · -- n < 807733812
              exact Brocard.berndt_galway_chunk_4491 n m (by omega) (by omega) h
            · -- n >= 807733812
              exact Brocard.berndt_galway_chunk_4492 n m (by omega) (by omega) h
          · -- n >= 807913669
            exact Brocard.berndt_galway_chunk_4493 n m (by omega) (by omega) h
        · -- n >= 808093525
          rcases Nat.lt_or_ge n 808273381 with hs4 | hs4
          · -- n < 808273381
            exact Brocard.berndt_galway_chunk_4494 n m (by omega) (by omega) h
          · -- n >= 808273381
            exact Brocard.berndt_galway_chunk_4495 n m (by omega) (by omega) h
