-- Prove2me | solution 1 for Brocard.berndt_galway_group_075
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:53:37.574921+00:00
-- url     : https://prove2.me/submissions/85f53dea-c951-4bba-bb78-59fa227b93fa

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_3431
import Theorems.Thm_Brocard_berndt_galway_chunk_3432
import Theorems.Thm_Brocard_berndt_galway_chunk_3433
import Theorems.Thm_Brocard_berndt_galway_chunk_3434
import Theorems.Thm_Brocard_berndt_galway_chunk_3435
import Theorems.Thm_Brocard_berndt_galway_chunk_3436
import Theorems.Thm_Brocard_berndt_galway_chunk_3437
import Theorems.Thm_Brocard_berndt_galway_chunk_3438
import Theorems.Thm_Brocard_berndt_galway_chunk_3439
import Theorems.Thm_Brocard_berndt_galway_chunk_3440
import Theorems.Thm_Brocard_berndt_galway_chunk_3441
import Theorems.Thm_Brocard_berndt_galway_chunk_3442
import Theorems.Thm_Brocard_berndt_galway_chunk_3443
import Theorems.Thm_Brocard_berndt_galway_chunk_3444
import Theorems.Thm_Brocard_berndt_galway_chunk_3445
import Theorems.Thm_Brocard_berndt_galway_chunk_3446
import Theorems.Thm_Brocard_berndt_galway_chunk_3447
import Theorems.Thm_Brocard_berndt_galway_chunk_3448
import Theorems.Thm_Brocard_berndt_galway_chunk_3449
import Theorems.Thm_Brocard_berndt_galway_chunk_3450
import Theorems.Thm_Brocard_berndt_galway_chunk_3451
import Theorems.Thm_Brocard_berndt_galway_chunk_3452
import Theorems.Thm_Brocard_berndt_galway_chunk_3453
import Theorems.Thm_Brocard_berndt_galway_chunk_3454
import Theorems.Thm_Brocard_berndt_galway_chunk_3455
import Theorems.Thm_Brocard_berndt_galway_chunk_3456
import Theorems.Thm_Brocard_berndt_galway_chunk_3457
import Theorems.Thm_Brocard_berndt_galway_chunk_3458
import Theorems.Thm_Brocard_berndt_galway_chunk_3459
import Theorems.Thm_Brocard_berndt_galway_chunk_3460
import Theorems.Thm_Brocard_berndt_galway_chunk_3461
import Theorems.Thm_Brocard_berndt_galway_chunk_3462
import Theorems.Thm_Brocard_berndt_galway_chunk_3463
import Theorems.Thm_Brocard_berndt_galway_chunk_3464
import Theorems.Thm_Brocard_berndt_galway_chunk_3465
import Theorems.Thm_Brocard_berndt_galway_chunk_3466
import Theorems.Thm_Brocard_berndt_galway_chunk_3467
import Theorems.Thm_Brocard_berndt_galway_chunk_3468
import Theorems.Thm_Brocard_berndt_galway_chunk_3469
import Theorems.Thm_Brocard_berndt_galway_chunk_3470
import Theorems.Thm_Brocard_berndt_galway_chunk_3471
import Theorems.Thm_Brocard_berndt_galway_chunk_3472
import Theorems.Thm_Brocard_berndt_galway_chunk_3473
import Theorems.Thm_Brocard_berndt_galway_chunk_3474
import Theorems.Thm_Brocard_berndt_galway_chunk_3475
import Theorems.Thm_Brocard_berndt_galway_chunk_3476
import Theorems.Thm_Brocard_berndt_galway_chunk_3477

theorem solution (n m : ℕ) (h1 : 616906474 ≤ n) (h2 : n < 625359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 621223021 with hs0 | hs0
  · -- n < 621223021
    rcases Nat.lt_or_ge n 619064748 with hs1 | hs1
    · -- n < 619064748
      rcases Nat.lt_or_ge n 617985611 with hs2 | hs2
      · -- n < 617985611
        rcases Nat.lt_or_ge n 617446043 with hs3 | hs3
        · -- n < 617446043
          rcases Nat.lt_or_ge n 617266187 with hs4 | hs4
          · -- n < 617266187
            rcases Nat.lt_or_ge n 617086330 with hs5 | hs5
            · -- n < 617086330
              exact Brocard.berndt_galway_chunk_3431 n m (by omega) (by omega) h
            · -- n >= 617086330
              exact Brocard.berndt_galway_chunk_3432 n m (by omega) (by omega) h
          · -- n >= 617266187
            exact Brocard.berndt_galway_chunk_3433 n m (by omega) (by omega) h
        · -- n >= 617446043
          rcases Nat.lt_or_ge n 617805755 with hs4 | hs4
          · -- n < 617805755
            rcases Nat.lt_or_ge n 617625899 with hs5 | hs5
            · -- n < 617625899
              exact Brocard.berndt_galway_chunk_3434 n m (by omega) (by omega) h
            · -- n >= 617625899
              exact Brocard.berndt_galway_chunk_3435 n m (by omega) (by omega) h
          · -- n >= 617805755
            exact Brocard.berndt_galway_chunk_3436 n m (by omega) (by omega) h
      · -- n >= 617985611
        rcases Nat.lt_or_ge n 618525179 with hs3 | hs3
        · -- n < 618525179
          rcases Nat.lt_or_ge n 618345323 with hs4 | hs4
          · -- n < 618345323
            rcases Nat.lt_or_ge n 618165467 with hs5 | hs5
            · -- n < 618165467
              exact Brocard.berndt_galway_chunk_3437 n m (by omega) (by omega) h
            · -- n >= 618165467
              exact Brocard.berndt_galway_chunk_3438 n m (by omega) (by omega) h
          · -- n >= 618345323
            exact Brocard.berndt_galway_chunk_3439 n m (by omega) (by omega) h
        · -- n >= 618525179
          rcases Nat.lt_or_ge n 618884892 with hs4 | hs4
          · -- n < 618884892
            rcases Nat.lt_or_ge n 618705035 with hs5 | hs5
            · -- n < 618705035
              exact Brocard.berndt_galway_chunk_3440 n m (by omega) (by omega) h
            · -- n >= 618705035
              exact Brocard.berndt_galway_chunk_3441 n m (by omega) (by omega) h
          · -- n >= 618884892
            exact Brocard.berndt_galway_chunk_3442 n m (by omega) (by omega) h
    · -- n >= 619064748
      rcases Nat.lt_or_ge n 620143884 with hs2 | hs2
      · -- n < 620143884
        rcases Nat.lt_or_ge n 619604316 with hs3 | hs3
        · -- n < 619604316
          rcases Nat.lt_or_ge n 619424460 with hs4 | hs4
          · -- n < 619424460
            rcases Nat.lt_or_ge n 619244604 with hs5 | hs5
            · -- n < 619244604
              exact Brocard.berndt_galway_chunk_3443 n m (by omega) (by omega) h
            · -- n >= 619244604
              exact Brocard.berndt_galway_chunk_3444 n m (by omega) (by omega) h
          · -- n >= 619424460
            exact Brocard.berndt_galway_chunk_3445 n m (by omega) (by omega) h
        · -- n >= 619604316
          rcases Nat.lt_or_ge n 619964028 with hs4 | hs4
          · -- n < 619964028
            rcases Nat.lt_or_ge n 619784172 with hs5 | hs5
            · -- n < 619784172
              exact Brocard.berndt_galway_chunk_3446 n m (by omega) (by omega) h
            · -- n >= 619784172
              exact Brocard.berndt_galway_chunk_3447 n m (by omega) (by omega) h
          · -- n >= 619964028
            exact Brocard.berndt_galway_chunk_3448 n m (by omega) (by omega) h
      · -- n >= 620143884
        rcases Nat.lt_or_ge n 620683453 with hs3 | hs3
        · -- n < 620683453
          rcases Nat.lt_or_ge n 620503597 with hs4 | hs4
          · -- n < 620503597
            rcases Nat.lt_or_ge n 620323741 with hs5 | hs5
            · -- n < 620323741
              exact Brocard.berndt_galway_chunk_3449 n m (by omega) (by omega) h
            · -- n >= 620323741
              exact Brocard.berndt_galway_chunk_3450 n m (by omega) (by omega) h
          · -- n >= 620503597
            exact Brocard.berndt_galway_chunk_3451 n m (by omega) (by omega) h
        · -- n >= 620683453
          rcases Nat.lt_or_ge n 621043165 with hs4 | hs4
          · -- n < 621043165
            rcases Nat.lt_or_ge n 620863309 with hs5 | hs5
            · -- n < 620863309
              exact Brocard.berndt_galway_chunk_3452 n m (by omega) (by omega) h
            · -- n >= 620863309
              exact Brocard.berndt_galway_chunk_3453 n m (by omega) (by omega) h
          · -- n >= 621043165
            exact Brocard.berndt_galway_chunk_3454 n m (by omega) (by omega) h
  · -- n >= 621223021
    rcases Nat.lt_or_ge n 623381294 with hs1 | hs1
    · -- n < 623381294
      rcases Nat.lt_or_ge n 622302158 with hs2 | hs2
      · -- n < 622302158
        rcases Nat.lt_or_ge n 621762589 with hs3 | hs3
        · -- n < 621762589
          rcases Nat.lt_or_ge n 621582733 with hs4 | hs4
          · -- n < 621582733
            rcases Nat.lt_or_ge n 621402877 with hs5 | hs5
            · -- n < 621402877
              exact Brocard.berndt_galway_chunk_3455 n m (by omega) (by omega) h
            · -- n >= 621402877
              exact Brocard.berndt_galway_chunk_3456 n m (by omega) (by omega) h
          · -- n >= 621582733
            exact Brocard.berndt_galway_chunk_3457 n m (by omega) (by omega) h
        · -- n >= 621762589
          rcases Nat.lt_or_ge n 622122302 with hs4 | hs4
          · -- n < 622122302
            rcases Nat.lt_or_ge n 621942446 with hs5 | hs5
            · -- n < 621942446
              exact Brocard.berndt_galway_chunk_3458 n m (by omega) (by omega) h
            · -- n >= 621942446
              exact Brocard.berndt_galway_chunk_3459 n m (by omega) (by omega) h
          · -- n >= 622122302
            exact Brocard.berndt_galway_chunk_3460 n m (by omega) (by omega) h
      · -- n >= 622302158
        rcases Nat.lt_or_ge n 622841726 with hs3 | hs3
        · -- n < 622841726
          rcases Nat.lt_or_ge n 622661870 with hs4 | hs4
          · -- n < 622661870
            rcases Nat.lt_or_ge n 622482014 with hs5 | hs5
            · -- n < 622482014
              exact Brocard.berndt_galway_chunk_3461 n m (by omega) (by omega) h
            · -- n >= 622482014
              exact Brocard.berndt_galway_chunk_3462 n m (by omega) (by omega) h
          · -- n >= 622661870
            exact Brocard.berndt_galway_chunk_3463 n m (by omega) (by omega) h
        · -- n >= 622841726
          rcases Nat.lt_or_ge n 623201438 with hs4 | hs4
          · -- n < 623201438
            rcases Nat.lt_or_ge n 623021582 with hs5 | hs5
            · -- n < 623021582
              exact Brocard.berndt_galway_chunk_3464 n m (by omega) (by omega) h
            · -- n >= 623021582
              exact Brocard.berndt_galway_chunk_3465 n m (by omega) (by omega) h
          · -- n >= 623201438
            exact Brocard.berndt_galway_chunk_3466 n m (by omega) (by omega) h
    · -- n >= 623381294
      rcases Nat.lt_or_ge n 624460431 with hs2 | hs2
      · -- n < 624460431
        rcases Nat.lt_or_ge n 623920863 with hs3 | hs3
        · -- n < 623920863
          rcases Nat.lt_or_ge n 623741007 with hs4 | hs4
          · -- n < 623741007
            rcases Nat.lt_or_ge n 623561151 with hs5 | hs5
            · -- n < 623561151
              exact Brocard.berndt_galway_chunk_3467 n m (by omega) (by omega) h
            · -- n >= 623561151
              exact Brocard.berndt_galway_chunk_3468 n m (by omega) (by omega) h
          · -- n >= 623741007
            exact Brocard.berndt_galway_chunk_3469 n m (by omega) (by omega) h
        · -- n >= 623920863
          rcases Nat.lt_or_ge n 624280575 with hs4 | hs4
          · -- n < 624280575
            rcases Nat.lt_or_ge n 624100719 with hs5 | hs5
            · -- n < 624100719
              exact Brocard.berndt_galway_chunk_3470 n m (by omega) (by omega) h
            · -- n >= 624100719
              exact Brocard.berndt_galway_chunk_3471 n m (by omega) (by omega) h
          · -- n >= 624280575
            exact Brocard.berndt_galway_chunk_3472 n m (by omega) (by omega) h
      · -- n >= 624460431
        rcases Nat.lt_or_ge n 625000000 with hs3 | hs3
        · -- n < 625000000
          rcases Nat.lt_or_ge n 624820143 with hs4 | hs4
          · -- n < 624820143
            rcases Nat.lt_or_ge n 624640287 with hs5 | hs5
            · -- n < 624640287
              exact Brocard.berndt_galway_chunk_3473 n m (by omega) (by omega) h
            · -- n >= 624640287
              exact Brocard.berndt_galway_chunk_3474 n m (by omega) (by omega) h
          · -- n >= 624820143
            exact Brocard.berndt_galway_chunk_3475 n m (by omega) (by omega) h
        · -- n >= 625000000
          rcases Nat.lt_or_ge n 625179856 with hs4 | hs4
          · -- n < 625179856
            exact Brocard.berndt_galway_chunk_3476 n m (by omega) (by omega) h
          · -- n >= 625179856
            exact Brocard.berndt_galway_chunk_3477 n m (by omega) (by omega) h
