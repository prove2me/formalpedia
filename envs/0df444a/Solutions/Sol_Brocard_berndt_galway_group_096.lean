-- Prove2me | solution 1 for Brocard.berndt_galway_group_096
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:48:14.529381+00:00
-- url     : https://prove2.me/submissions/a38094d0-3ed9-4760-958e-82a2cb701ca5

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_4403
import Theorems.Thm_Brocard_berndt_galway_chunk_4404
import Theorems.Thm_Brocard_berndt_galway_chunk_4405
import Theorems.Thm_Brocard_berndt_galway_chunk_4406
import Theorems.Thm_Brocard_berndt_galway_chunk_4407
import Theorems.Thm_Brocard_berndt_galway_chunk_4408
import Theorems.Thm_Brocard_berndt_galway_chunk_4409
import Theorems.Thm_Brocard_berndt_galway_chunk_4410
import Theorems.Thm_Brocard_berndt_galway_chunk_4411
import Theorems.Thm_Brocard_berndt_galway_chunk_4412
import Theorems.Thm_Brocard_berndt_galway_chunk_4413
import Theorems.Thm_Brocard_berndt_galway_chunk_4414
import Theorems.Thm_Brocard_berndt_galway_chunk_4415
import Theorems.Thm_Brocard_berndt_galway_chunk_4416
import Theorems.Thm_Brocard_berndt_galway_chunk_4417
import Theorems.Thm_Brocard_berndt_galway_chunk_4418
import Theorems.Thm_Brocard_berndt_galway_chunk_4419
import Theorems.Thm_Brocard_berndt_galway_chunk_4420
import Theorems.Thm_Brocard_berndt_galway_chunk_4421
import Theorems.Thm_Brocard_berndt_galway_chunk_4422
import Theorems.Thm_Brocard_berndt_galway_chunk_4423
import Theorems.Thm_Brocard_berndt_galway_chunk_4424
import Theorems.Thm_Brocard_berndt_galway_chunk_4425
import Theorems.Thm_Brocard_berndt_galway_chunk_4426
import Theorems.Thm_Brocard_berndt_galway_chunk_4427
import Theorems.Thm_Brocard_berndt_galway_chunk_4428
import Theorems.Thm_Brocard_berndt_galway_chunk_4429
import Theorems.Thm_Brocard_berndt_galway_chunk_4430
import Theorems.Thm_Brocard_berndt_galway_chunk_4431
import Theorems.Thm_Brocard_berndt_galway_chunk_4432
import Theorems.Thm_Brocard_berndt_galway_chunk_4433
import Theorems.Thm_Brocard_berndt_galway_chunk_4434
import Theorems.Thm_Brocard_berndt_galway_chunk_4435
import Theorems.Thm_Brocard_berndt_galway_chunk_4436
import Theorems.Thm_Brocard_berndt_galway_chunk_4437
import Theorems.Thm_Brocard_berndt_galway_chunk_4438
import Theorems.Thm_Brocard_berndt_galway_chunk_4439
import Theorems.Thm_Brocard_berndt_galway_chunk_4440
import Theorems.Thm_Brocard_berndt_galway_chunk_4441
import Theorems.Thm_Brocard_berndt_galway_chunk_4442
import Theorems.Thm_Brocard_berndt_galway_chunk_4443
import Theorems.Thm_Brocard_berndt_galway_chunk_4444
import Theorems.Thm_Brocard_berndt_galway_chunk_4445
import Theorems.Thm_Brocard_berndt_galway_chunk_4446
import Theorems.Thm_Brocard_berndt_galway_chunk_4447
import Theorems.Thm_Brocard_berndt_galway_chunk_4448

theorem solution (n m : ℕ) (h1 : 791726618 ≤ n) (h2 : n < 800000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 795863309 with hs0 | hs0
  · -- n < 795863309
    rcases Nat.lt_or_ge n 793884892 with hs1 | hs1
    · -- n < 793884892
      rcases Nat.lt_or_ge n 792805755 with hs2 | hs2
      · -- n < 792805755
        rcases Nat.lt_or_ge n 792266187 with hs3 | hs3
        · -- n < 792266187
          rcases Nat.lt_or_ge n 792086330 with hs4 | hs4
          · -- n < 792086330
            rcases Nat.lt_or_ge n 791906474 with hs5 | hs5
            · -- n < 791906474
              exact Brocard.berndt_galway_chunk_4403 n m (by omega) (by omega) h
            · -- n >= 791906474
              exact Brocard.berndt_galway_chunk_4404 n m (by omega) (by omega) h
          · -- n >= 792086330
            exact Brocard.berndt_galway_chunk_4405 n m (by omega) (by omega) h
        · -- n >= 792266187
          rcases Nat.lt_or_ge n 792625899 with hs4 | hs4
          · -- n < 792625899
            rcases Nat.lt_or_ge n 792446043 with hs5 | hs5
            · -- n < 792446043
              exact Brocard.berndt_galway_chunk_4406 n m (by omega) (by omega) h
            · -- n >= 792446043
              exact Brocard.berndt_galway_chunk_4407 n m (by omega) (by omega) h
          · -- n >= 792625899
            exact Brocard.berndt_galway_chunk_4408 n m (by omega) (by omega) h
      · -- n >= 792805755
        rcases Nat.lt_or_ge n 793345323 with hs3 | hs3
        · -- n < 793345323
          rcases Nat.lt_or_ge n 793165467 with hs4 | hs4
          · -- n < 793165467
            rcases Nat.lt_or_ge n 792985611 with hs5 | hs5
            · -- n < 792985611
              exact Brocard.berndt_galway_chunk_4409 n m (by omega) (by omega) h
            · -- n >= 792985611
              exact Brocard.berndt_galway_chunk_4410 n m (by omega) (by omega) h
          · -- n >= 793165467
            exact Brocard.berndt_galway_chunk_4411 n m (by omega) (by omega) h
        · -- n >= 793345323
          rcases Nat.lt_or_ge n 793705035 with hs4 | hs4
          · -- n < 793705035
            rcases Nat.lt_or_ge n 793525179 with hs5 | hs5
            · -- n < 793525179
              exact Brocard.berndt_galway_chunk_4412 n m (by omega) (by omega) h
            · -- n >= 793525179
              exact Brocard.berndt_galway_chunk_4413 n m (by omega) (by omega) h
          · -- n >= 793705035
            exact Brocard.berndt_galway_chunk_4414 n m (by omega) (by omega) h
    · -- n >= 793884892
      rcases Nat.lt_or_ge n 794964028 with hs2 | hs2
      · -- n < 794964028
        rcases Nat.lt_or_ge n 794424460 with hs3 | hs3
        · -- n < 794424460
          rcases Nat.lt_or_ge n 794244604 with hs4 | hs4
          · -- n < 794244604
            rcases Nat.lt_or_ge n 794064748 with hs5 | hs5
            · -- n < 794064748
              exact Brocard.berndt_galway_chunk_4415 n m (by omega) (by omega) h
            · -- n >= 794064748
              exact Brocard.berndt_galway_chunk_4416 n m (by omega) (by omega) h
          · -- n >= 794244604
            exact Brocard.berndt_galway_chunk_4417 n m (by omega) (by omega) h
        · -- n >= 794424460
          rcases Nat.lt_or_ge n 794784172 with hs4 | hs4
          · -- n < 794784172
            rcases Nat.lt_or_ge n 794604316 with hs5 | hs5
            · -- n < 794604316
              exact Brocard.berndt_galway_chunk_4418 n m (by omega) (by omega) h
            · -- n >= 794604316
              exact Brocard.berndt_galway_chunk_4419 n m (by omega) (by omega) h
          · -- n >= 794784172
            exact Brocard.berndt_galway_chunk_4420 n m (by omega) (by omega) h
      · -- n >= 794964028
        rcases Nat.lt_or_ge n 795503597 with hs3 | hs3
        · -- n < 795503597
          rcases Nat.lt_or_ge n 795323741 with hs4 | hs4
          · -- n < 795323741
            rcases Nat.lt_or_ge n 795143884 with hs5 | hs5
            · -- n < 795143884
              exact Brocard.berndt_galway_chunk_4421 n m (by omega) (by omega) h
            · -- n >= 795143884
              exact Brocard.berndt_galway_chunk_4422 n m (by omega) (by omega) h
          · -- n >= 795323741
            exact Brocard.berndt_galway_chunk_4423 n m (by omega) (by omega) h
        · -- n >= 795503597
          rcases Nat.lt_or_ge n 795683453 with hs4 | hs4
          · -- n < 795683453
            exact Brocard.berndt_galway_chunk_4424 n m (by omega) (by omega) h
          · -- n >= 795683453
            exact Brocard.berndt_galway_chunk_4425 n m (by omega) (by omega) h
  · -- n >= 795863309
    rcases Nat.lt_or_ge n 798021582 with hs1 | hs1
    · -- n < 798021582
      rcases Nat.lt_or_ge n 796942446 with hs2 | hs2
      · -- n < 796942446
        rcases Nat.lt_or_ge n 796402877 with hs3 | hs3
        · -- n < 796402877
          rcases Nat.lt_or_ge n 796223021 with hs4 | hs4
          · -- n < 796223021
            rcases Nat.lt_or_ge n 796043165 with hs5 | hs5
            · -- n < 796043165
              exact Brocard.berndt_galway_chunk_4426 n m (by omega) (by omega) h
            · -- n >= 796043165
              exact Brocard.berndt_galway_chunk_4427 n m (by omega) (by omega) h
          · -- n >= 796223021
            exact Brocard.berndt_galway_chunk_4428 n m (by omega) (by omega) h
        · -- n >= 796402877
          rcases Nat.lt_or_ge n 796762589 with hs4 | hs4
          · -- n < 796762589
            rcases Nat.lt_or_ge n 796582733 with hs5 | hs5
            · -- n < 796582733
              exact Brocard.berndt_galway_chunk_4429 n m (by omega) (by omega) h
            · -- n >= 796582733
              exact Brocard.berndt_galway_chunk_4430 n m (by omega) (by omega) h
          · -- n >= 796762589
            exact Brocard.berndt_galway_chunk_4431 n m (by omega) (by omega) h
      · -- n >= 796942446
        rcases Nat.lt_or_ge n 797482014 with hs3 | hs3
        · -- n < 797482014
          rcases Nat.lt_or_ge n 797302158 with hs4 | hs4
          · -- n < 797302158
            rcases Nat.lt_or_ge n 797122302 with hs5 | hs5
            · -- n < 797122302
              exact Brocard.berndt_galway_chunk_4432 n m (by omega) (by omega) h
            · -- n >= 797122302
              exact Brocard.berndt_galway_chunk_4433 n m (by omega) (by omega) h
          · -- n >= 797302158
            exact Brocard.berndt_galway_chunk_4434 n m (by omega) (by omega) h
        · -- n >= 797482014
          rcases Nat.lt_or_ge n 797841726 with hs4 | hs4
          · -- n < 797841726
            rcases Nat.lt_or_ge n 797661870 with hs5 | hs5
            · -- n < 797661870
              exact Brocard.berndt_galway_chunk_4435 n m (by omega) (by omega) h
            · -- n >= 797661870
              exact Brocard.berndt_galway_chunk_4436 n m (by omega) (by omega) h
          · -- n >= 797841726
            exact Brocard.berndt_galway_chunk_4437 n m (by omega) (by omega) h
    · -- n >= 798021582
      rcases Nat.lt_or_ge n 799100719 with hs2 | hs2
      · -- n < 799100719
        rcases Nat.lt_or_ge n 798561151 with hs3 | hs3
        · -- n < 798561151
          rcases Nat.lt_or_ge n 798381294 with hs4 | hs4
          · -- n < 798381294
            rcases Nat.lt_or_ge n 798201438 with hs5 | hs5
            · -- n < 798201438
              exact Brocard.berndt_galway_chunk_4438 n m (by omega) (by omega) h
            · -- n >= 798201438
              exact Brocard.berndt_galway_chunk_4439 n m (by omega) (by omega) h
          · -- n >= 798381294
            exact Brocard.berndt_galway_chunk_4440 n m (by omega) (by omega) h
        · -- n >= 798561151
          rcases Nat.lt_or_ge n 798920863 with hs4 | hs4
          · -- n < 798920863
            rcases Nat.lt_or_ge n 798741007 with hs5 | hs5
            · -- n < 798741007
              exact Brocard.berndt_galway_chunk_4441 n m (by omega) (by omega) h
            · -- n >= 798741007
              exact Brocard.berndt_galway_chunk_4442 n m (by omega) (by omega) h
          · -- n >= 798920863
            exact Brocard.berndt_galway_chunk_4443 n m (by omega) (by omega) h
      · -- n >= 799100719
        rcases Nat.lt_or_ge n 799640287 with hs3 | hs3
        · -- n < 799640287
          rcases Nat.lt_or_ge n 799460431 with hs4 | hs4
          · -- n < 799460431
            rcases Nat.lt_or_ge n 799280575 with hs5 | hs5
            · -- n < 799280575
              exact Brocard.berndt_galway_chunk_4444 n m (by omega) (by omega) h
            · -- n >= 799280575
              exact Brocard.berndt_galway_chunk_4445 n m (by omega) (by omega) h
          · -- n >= 799460431
            exact Brocard.berndt_galway_chunk_4446 n m (by omega) (by omega) h
        · -- n >= 799640287
          rcases Nat.lt_or_ge n 799820143 with hs4 | hs4
          · -- n < 799820143
            exact Brocard.berndt_galway_chunk_4447 n m (by omega) (by omega) h
          · -- n >= 799820143
            exact Brocard.berndt_galway_chunk_4448 n m (by omega) (by omega) h
