-- Prove2me | solution 1 for Brocard.berndt_galway_group_118
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:06:59.93348+00:00
-- url     : https://prove2.me/submissions/05bcde52-b94d-4025-b158-919d6de70963

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_5423
import Theorems.Thm_Brocard_berndt_galway_chunk_5424
import Theorems.Thm_Brocard_berndt_galway_chunk_5425
import Theorems.Thm_Brocard_berndt_galway_chunk_5426
import Theorems.Thm_Brocard_berndt_galway_chunk_5427
import Theorems.Thm_Brocard_berndt_galway_chunk_5428
import Theorems.Thm_Brocard_berndt_galway_chunk_5429
import Theorems.Thm_Brocard_berndt_galway_chunk_5430
import Theorems.Thm_Brocard_berndt_galway_chunk_5431
import Theorems.Thm_Brocard_berndt_galway_chunk_5432
import Theorems.Thm_Brocard_berndt_galway_chunk_5433
import Theorems.Thm_Brocard_berndt_galway_chunk_5434
import Theorems.Thm_Brocard_berndt_galway_chunk_5435
import Theorems.Thm_Brocard_berndt_galway_chunk_5436
import Theorems.Thm_Brocard_berndt_galway_chunk_5437
import Theorems.Thm_Brocard_berndt_galway_chunk_5438
import Theorems.Thm_Brocard_berndt_galway_chunk_5439
import Theorems.Thm_Brocard_berndt_galway_chunk_5440
import Theorems.Thm_Brocard_berndt_galway_chunk_5441
import Theorems.Thm_Brocard_berndt_galway_chunk_5442
import Theorems.Thm_Brocard_berndt_galway_chunk_5443
import Theorems.Thm_Brocard_berndt_galway_chunk_5444
import Theorems.Thm_Brocard_berndt_galway_chunk_5445
import Theorems.Thm_Brocard_berndt_galway_chunk_5446
import Theorems.Thm_Brocard_berndt_galway_chunk_5447
import Theorems.Thm_Brocard_berndt_galway_chunk_5448
import Theorems.Thm_Brocard_berndt_galway_chunk_5449
import Theorems.Thm_Brocard_berndt_galway_chunk_5450
import Theorems.Thm_Brocard_berndt_galway_chunk_5451
import Theorems.Thm_Brocard_berndt_galway_chunk_5452
import Theorems.Thm_Brocard_berndt_galway_chunk_5453
import Theorems.Thm_Brocard_berndt_galway_chunk_5454
import Theorems.Thm_Brocard_berndt_galway_chunk_5455
import Theorems.Thm_Brocard_berndt_galway_chunk_5456
import Theorems.Thm_Brocard_berndt_galway_chunk_5457
import Theorems.Thm_Brocard_berndt_galway_chunk_5458
import Theorems.Thm_Brocard_berndt_galway_chunk_5459
import Theorems.Thm_Brocard_berndt_galway_chunk_5460
import Theorems.Thm_Brocard_berndt_galway_chunk_5461
import Theorems.Thm_Brocard_berndt_galway_chunk_5462
import Theorems.Thm_Brocard_berndt_galway_chunk_5463
import Theorems.Thm_Brocard_berndt_galway_chunk_5464
import Theorems.Thm_Brocard_berndt_galway_chunk_5465
import Theorems.Thm_Brocard_berndt_galway_chunk_5466
import Theorems.Thm_Brocard_berndt_galway_chunk_5467
import Theorems.Thm_Brocard_berndt_galway_chunk_5468

theorem solution (n m : ℕ) (h1 : 975179856 ≤ n) (h2 : n < 983453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 979316546 with hs0 | hs0
  · -- n < 979316546
    rcases Nat.lt_or_ge n 977338129 with hs1 | hs1
    · -- n < 977338129
      rcases Nat.lt_or_ge n 976258992 with hs2 | hs2
      · -- n < 976258992
        rcases Nat.lt_or_ge n 975719424 with hs3 | hs3
        · -- n < 975719424
          rcases Nat.lt_or_ge n 975539568 with hs4 | hs4
          · -- n < 975539568
            rcases Nat.lt_or_ge n 975359712 with hs5 | hs5
            · -- n < 975359712
              exact Brocard.berndt_galway_chunk_5423 n m (by omega) (by omega) h
            · -- n >= 975359712
              exact Brocard.berndt_galway_chunk_5424 n m (by omega) (by omega) h
          · -- n >= 975539568
            exact Brocard.berndt_galway_chunk_5425 n m (by omega) (by omega) h
        · -- n >= 975719424
          rcases Nat.lt_or_ge n 976079136 with hs4 | hs4
          · -- n < 976079136
            rcases Nat.lt_or_ge n 975899280 with hs5 | hs5
            · -- n < 975899280
              exact Brocard.berndt_galway_chunk_5426 n m (by omega) (by omega) h
            · -- n >= 975899280
              exact Brocard.berndt_galway_chunk_5427 n m (by omega) (by omega) h
          · -- n >= 976079136
            exact Brocard.berndt_galway_chunk_5428 n m (by omega) (by omega) h
      · -- n >= 976258992
        rcases Nat.lt_or_ge n 976798561 with hs3 | hs3
        · -- n < 976798561
          rcases Nat.lt_or_ge n 976618705 with hs4 | hs4
          · -- n < 976618705
            rcases Nat.lt_or_ge n 976438848 with hs5 | hs5
            · -- n < 976438848
              exact Brocard.berndt_galway_chunk_5429 n m (by omega) (by omega) h
            · -- n >= 976438848
              exact Brocard.berndt_galway_chunk_5430 n m (by omega) (by omega) h
          · -- n >= 976618705
            exact Brocard.berndt_galway_chunk_5431 n m (by omega) (by omega) h
        · -- n >= 976798561
          rcases Nat.lt_or_ge n 977158273 with hs4 | hs4
          · -- n < 977158273
            rcases Nat.lt_or_ge n 976978417 with hs5 | hs5
            · -- n < 976978417
              exact Brocard.berndt_galway_chunk_5432 n m (by omega) (by omega) h
            · -- n >= 976978417
              exact Brocard.berndt_galway_chunk_5433 n m (by omega) (by omega) h
          · -- n >= 977158273
            exact Brocard.berndt_galway_chunk_5434 n m (by omega) (by omega) h
    · -- n >= 977338129
      rcases Nat.lt_or_ge n 978417266 with hs2 | hs2
      · -- n < 978417266
        rcases Nat.lt_or_ge n 977877697 with hs3 | hs3
        · -- n < 977877697
          rcases Nat.lt_or_ge n 977697841 with hs4 | hs4
          · -- n < 977697841
            rcases Nat.lt_or_ge n 977517985 with hs5 | hs5
            · -- n < 977517985
              exact Brocard.berndt_galway_chunk_5435 n m (by omega) (by omega) h
            · -- n >= 977517985
              exact Brocard.berndt_galway_chunk_5436 n m (by omega) (by omega) h
          · -- n >= 977697841
            exact Brocard.berndt_galway_chunk_5437 n m (by omega) (by omega) h
        · -- n >= 977877697
          rcases Nat.lt_or_ge n 978237410 with hs4 | hs4
          · -- n < 978237410
            rcases Nat.lt_or_ge n 978057553 with hs5 | hs5
            · -- n < 978057553
              exact Brocard.berndt_galway_chunk_5438 n m (by omega) (by omega) h
            · -- n >= 978057553
              exact Brocard.berndt_galway_chunk_5439 n m (by omega) (by omega) h
          · -- n >= 978237410
            exact Brocard.berndt_galway_chunk_5440 n m (by omega) (by omega) h
      · -- n >= 978417266
        rcases Nat.lt_or_ge n 978956834 with hs3 | hs3
        · -- n < 978956834
          rcases Nat.lt_or_ge n 978776978 with hs4 | hs4
          · -- n < 978776978
            rcases Nat.lt_or_ge n 978597122 with hs5 | hs5
            · -- n < 978597122
              exact Brocard.berndt_galway_chunk_5441 n m (by omega) (by omega) h
            · -- n >= 978597122
              exact Brocard.berndt_galway_chunk_5442 n m (by omega) (by omega) h
          · -- n >= 978776978
            exact Brocard.berndt_galway_chunk_5443 n m (by omega) (by omega) h
        · -- n >= 978956834
          rcases Nat.lt_or_ge n 979136690 with hs4 | hs4
          · -- n < 979136690
            exact Brocard.berndt_galway_chunk_5444 n m (by omega) (by omega) h
          · -- n >= 979136690
            exact Brocard.berndt_galway_chunk_5445 n m (by omega) (by omega) h
  · -- n >= 979316546
    rcases Nat.lt_or_ge n 981474820 with hs1 | hs1
    · -- n < 981474820
      rcases Nat.lt_or_ge n 980395683 with hs2 | hs2
      · -- n < 980395683
        rcases Nat.lt_or_ge n 979856115 with hs3 | hs3
        · -- n < 979856115
          rcases Nat.lt_or_ge n 979676258 with hs4 | hs4
          · -- n < 979676258
            rcases Nat.lt_or_ge n 979496402 with hs5 | hs5
            · -- n < 979496402
              exact Brocard.berndt_galway_chunk_5446 n m (by omega) (by omega) h
            · -- n >= 979496402
              exact Brocard.berndt_galway_chunk_5447 n m (by omega) (by omega) h
          · -- n >= 979676258
            exact Brocard.berndt_galway_chunk_5448 n m (by omega) (by omega) h
        · -- n >= 979856115
          rcases Nat.lt_or_ge n 980215827 with hs4 | hs4
          · -- n < 980215827
            rcases Nat.lt_or_ge n 980035971 with hs5 | hs5
            · -- n < 980035971
              exact Brocard.berndt_galway_chunk_5449 n m (by omega) (by omega) h
            · -- n >= 980035971
              exact Brocard.berndt_galway_chunk_5450 n m (by omega) (by omega) h
          · -- n >= 980215827
            exact Brocard.berndt_galway_chunk_5451 n m (by omega) (by omega) h
      · -- n >= 980395683
        rcases Nat.lt_or_ge n 980935251 with hs3 | hs3
        · -- n < 980935251
          rcases Nat.lt_or_ge n 980755395 with hs4 | hs4
          · -- n < 980755395
            rcases Nat.lt_or_ge n 980575539 with hs5 | hs5
            · -- n < 980575539
              exact Brocard.berndt_galway_chunk_5452 n m (by omega) (by omega) h
            · -- n >= 980575539
              exact Brocard.berndt_galway_chunk_5453 n m (by omega) (by omega) h
          · -- n >= 980755395
            exact Brocard.berndt_galway_chunk_5454 n m (by omega) (by omega) h
        · -- n >= 980935251
          rcases Nat.lt_or_ge n 981294964 with hs4 | hs4
          · -- n < 981294964
            rcases Nat.lt_or_ge n 981115107 with hs5 | hs5
            · -- n < 981115107
              exact Brocard.berndt_galway_chunk_5455 n m (by omega) (by omega) h
            · -- n >= 981115107
              exact Brocard.berndt_galway_chunk_5456 n m (by omega) (by omega) h
          · -- n >= 981294964
            exact Brocard.berndt_galway_chunk_5457 n m (by omega) (by omega) h
    · -- n >= 981474820
      rcases Nat.lt_or_ge n 982553956 with hs2 | hs2
      · -- n < 982553956
        rcases Nat.lt_or_ge n 982014388 with hs3 | hs3
        · -- n < 982014388
          rcases Nat.lt_or_ge n 981834532 with hs4 | hs4
          · -- n < 981834532
            rcases Nat.lt_or_ge n 981654676 with hs5 | hs5
            · -- n < 981654676
              exact Brocard.berndt_galway_chunk_5458 n m (by omega) (by omega) h
            · -- n >= 981654676
              exact Brocard.berndt_galway_chunk_5459 n m (by omega) (by omega) h
          · -- n >= 981834532
            exact Brocard.berndt_galway_chunk_5460 n m (by omega) (by omega) h
        · -- n >= 982014388
          rcases Nat.lt_or_ge n 982374100 with hs4 | hs4
          · -- n < 982374100
            rcases Nat.lt_or_ge n 982194244 with hs5 | hs5
            · -- n < 982194244
              exact Brocard.berndt_galway_chunk_5461 n m (by omega) (by omega) h
            · -- n >= 982194244
              exact Brocard.berndt_galway_chunk_5462 n m (by omega) (by omega) h
          · -- n >= 982374100
            exact Brocard.berndt_galway_chunk_5463 n m (by omega) (by omega) h
      · -- n >= 982553956
        rcases Nat.lt_or_ge n 983093525 with hs3 | hs3
        · -- n < 983093525
          rcases Nat.lt_or_ge n 982913669 with hs4 | hs4
          · -- n < 982913669
            rcases Nat.lt_or_ge n 982733812 with hs5 | hs5
            · -- n < 982733812
              exact Brocard.berndt_galway_chunk_5464 n m (by omega) (by omega) h
            · -- n >= 982733812
              exact Brocard.berndt_galway_chunk_5465 n m (by omega) (by omega) h
          · -- n >= 982913669
            exact Brocard.berndt_galway_chunk_5466 n m (by omega) (by omega) h
        · -- n >= 983093525
          rcases Nat.lt_or_ge n 983273381 with hs4 | hs4
          · -- n < 983273381
            exact Brocard.berndt_galway_chunk_5467 n m (by omega) (by omega) h
          · -- n >= 983273381
            exact Brocard.berndt_galway_chunk_5468 n m (by omega) (by omega) h
