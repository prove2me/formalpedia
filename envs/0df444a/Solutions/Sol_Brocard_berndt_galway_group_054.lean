-- Prove2me | solution 1 for Brocard.berndt_galway_group_054
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:02:59.496+00:00
-- url     : https://prove2.me/submissions/012bf68a-441b-4de5-a01c-10486a23aa64

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_2459
import Theorems.Thm_Brocard_berndt_galway_chunk_2460
import Theorems.Thm_Brocard_berndt_galway_chunk_2461
import Theorems.Thm_Brocard_berndt_galway_chunk_2462
import Theorems.Thm_Brocard_berndt_galway_chunk_2463
import Theorems.Thm_Brocard_berndt_galway_chunk_2464
import Theorems.Thm_Brocard_berndt_galway_chunk_2465
import Theorems.Thm_Brocard_berndt_galway_chunk_2466
import Theorems.Thm_Brocard_berndt_galway_chunk_2467
import Theorems.Thm_Brocard_berndt_galway_chunk_2468
import Theorems.Thm_Brocard_berndt_galway_chunk_2469
import Theorems.Thm_Brocard_berndt_galway_chunk_2470
import Theorems.Thm_Brocard_berndt_galway_chunk_2471
import Theorems.Thm_Brocard_berndt_galway_chunk_2472
import Theorems.Thm_Brocard_berndt_galway_chunk_2473
import Theorems.Thm_Brocard_berndt_galway_chunk_2474
import Theorems.Thm_Brocard_berndt_galway_chunk_2475
import Theorems.Thm_Brocard_berndt_galway_chunk_2476
import Theorems.Thm_Brocard_berndt_galway_chunk_2477
import Theorems.Thm_Brocard_berndt_galway_chunk_2478
import Theorems.Thm_Brocard_berndt_galway_chunk_2479
import Theorems.Thm_Brocard_berndt_galway_chunk_2480
import Theorems.Thm_Brocard_berndt_galway_chunk_2481
import Theorems.Thm_Brocard_berndt_galway_chunk_2482
import Theorems.Thm_Brocard_berndt_galway_chunk_2483
import Theorems.Thm_Brocard_berndt_galway_chunk_2484
import Theorems.Thm_Brocard_berndt_galway_chunk_2485
import Theorems.Thm_Brocard_berndt_galway_chunk_2486
import Theorems.Thm_Brocard_berndt_galway_chunk_2487
import Theorems.Thm_Brocard_berndt_galway_chunk_2488
import Theorems.Thm_Brocard_berndt_galway_chunk_2489
import Theorems.Thm_Brocard_berndt_galway_chunk_2490
import Theorems.Thm_Brocard_berndt_galway_chunk_2491
import Theorems.Thm_Brocard_berndt_galway_chunk_2492
import Theorems.Thm_Brocard_berndt_galway_chunk_2493
import Theorems.Thm_Brocard_berndt_galway_chunk_2494
import Theorems.Thm_Brocard_berndt_galway_chunk_2495
import Theorems.Thm_Brocard_berndt_galway_chunk_2496
import Theorems.Thm_Brocard_berndt_galway_chunk_2497
import Theorems.Thm_Brocard_berndt_galway_chunk_2498
import Theorems.Thm_Brocard_berndt_galway_chunk_2499
import Theorems.Thm_Brocard_berndt_galway_chunk_2500
import Theorems.Thm_Brocard_berndt_galway_chunk_2501
import Theorems.Thm_Brocard_berndt_galway_chunk_2502
import Theorems.Thm_Brocard_berndt_galway_chunk_2503
import Theorems.Thm_Brocard_berndt_galway_chunk_2504

theorem solution (n m : ℕ) (h1 : 442086330 ≤ n) (h2 : n < 450359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 446223021 with hs0 | hs0
  · -- n < 446223021
    rcases Nat.lt_or_ge n 444244604 with hs1 | hs1
    · -- n < 444244604
      rcases Nat.lt_or_ge n 443165467 with hs2 | hs2
      · -- n < 443165467
        rcases Nat.lt_or_ge n 442625899 with hs3 | hs3
        · -- n < 442625899
          rcases Nat.lt_or_ge n 442446043 with hs4 | hs4
          · -- n < 442446043
            rcases Nat.lt_or_ge n 442266187 with hs5 | hs5
            · -- n < 442266187
              exact Brocard.berndt_galway_chunk_2459 n m (by omega) (by omega) h
            · -- n >= 442266187
              exact Brocard.berndt_galway_chunk_2460 n m (by omega) (by omega) h
          · -- n >= 442446043
            exact Brocard.berndt_galway_chunk_2461 n m (by omega) (by omega) h
        · -- n >= 442625899
          rcases Nat.lt_or_ge n 442985611 with hs4 | hs4
          · -- n < 442985611
            rcases Nat.lt_or_ge n 442805755 with hs5 | hs5
            · -- n < 442805755
              exact Brocard.berndt_galway_chunk_2462 n m (by omega) (by omega) h
            · -- n >= 442805755
              exact Brocard.berndt_galway_chunk_2463 n m (by omega) (by omega) h
          · -- n >= 442985611
            exact Brocard.berndt_galway_chunk_2464 n m (by omega) (by omega) h
      · -- n >= 443165467
        rcases Nat.lt_or_ge n 443705035 with hs3 | hs3
        · -- n < 443705035
          rcases Nat.lt_or_ge n 443525179 with hs4 | hs4
          · -- n < 443525179
            rcases Nat.lt_or_ge n 443345323 with hs5 | hs5
            · -- n < 443345323
              exact Brocard.berndt_galway_chunk_2465 n m (by omega) (by omega) h
            · -- n >= 443345323
              exact Brocard.berndt_galway_chunk_2466 n m (by omega) (by omega) h
          · -- n >= 443525179
            exact Brocard.berndt_galway_chunk_2467 n m (by omega) (by omega) h
        · -- n >= 443705035
          rcases Nat.lt_or_ge n 444064748 with hs4 | hs4
          · -- n < 444064748
            rcases Nat.lt_or_ge n 443884892 with hs5 | hs5
            · -- n < 443884892
              exact Brocard.berndt_galway_chunk_2468 n m (by omega) (by omega) h
            · -- n >= 443884892
              exact Brocard.berndt_galway_chunk_2469 n m (by omega) (by omega) h
          · -- n >= 444064748
            exact Brocard.berndt_galway_chunk_2470 n m (by omega) (by omega) h
    · -- n >= 444244604
      rcases Nat.lt_or_ge n 445323741 with hs2 | hs2
      · -- n < 445323741
        rcases Nat.lt_or_ge n 444784172 with hs3 | hs3
        · -- n < 444784172
          rcases Nat.lt_or_ge n 444604316 with hs4 | hs4
          · -- n < 444604316
            rcases Nat.lt_or_ge n 444424460 with hs5 | hs5
            · -- n < 444424460
              exact Brocard.berndt_galway_chunk_2471 n m (by omega) (by omega) h
            · -- n >= 444424460
              exact Brocard.berndt_galway_chunk_2472 n m (by omega) (by omega) h
          · -- n >= 444604316
            exact Brocard.berndt_galway_chunk_2473 n m (by omega) (by omega) h
        · -- n >= 444784172
          rcases Nat.lt_or_ge n 445143884 with hs4 | hs4
          · -- n < 445143884
            rcases Nat.lt_or_ge n 444964028 with hs5 | hs5
            · -- n < 444964028
              exact Brocard.berndt_galway_chunk_2474 n m (by omega) (by omega) h
            · -- n >= 444964028
              exact Brocard.berndt_galway_chunk_2475 n m (by omega) (by omega) h
          · -- n >= 445143884
            exact Brocard.berndt_galway_chunk_2476 n m (by omega) (by omega) h
      · -- n >= 445323741
        rcases Nat.lt_or_ge n 445863309 with hs3 | hs3
        · -- n < 445863309
          rcases Nat.lt_or_ge n 445683453 with hs4 | hs4
          · -- n < 445683453
            rcases Nat.lt_or_ge n 445503597 with hs5 | hs5
            · -- n < 445503597
              exact Brocard.berndt_galway_chunk_2477 n m (by omega) (by omega) h
            · -- n >= 445503597
              exact Brocard.berndt_galway_chunk_2478 n m (by omega) (by omega) h
          · -- n >= 445683453
            exact Brocard.berndt_galway_chunk_2479 n m (by omega) (by omega) h
        · -- n >= 445863309
          rcases Nat.lt_or_ge n 446043165 with hs4 | hs4
          · -- n < 446043165
            exact Brocard.berndt_galway_chunk_2480 n m (by omega) (by omega) h
          · -- n >= 446043165
            exact Brocard.berndt_galway_chunk_2481 n m (by omega) (by omega) h
  · -- n >= 446223021
    rcases Nat.lt_or_ge n 448381294 with hs1 | hs1
    · -- n < 448381294
      rcases Nat.lt_or_ge n 447302158 with hs2 | hs2
      · -- n < 447302158
        rcases Nat.lt_or_ge n 446762589 with hs3 | hs3
        · -- n < 446762589
          rcases Nat.lt_or_ge n 446582733 with hs4 | hs4
          · -- n < 446582733
            rcases Nat.lt_or_ge n 446402877 with hs5 | hs5
            · -- n < 446402877
              exact Brocard.berndt_galway_chunk_2482 n m (by omega) (by omega) h
            · -- n >= 446402877
              exact Brocard.berndt_galway_chunk_2483 n m (by omega) (by omega) h
          · -- n >= 446582733
            exact Brocard.berndt_galway_chunk_2484 n m (by omega) (by omega) h
        · -- n >= 446762589
          rcases Nat.lt_or_ge n 447122302 with hs4 | hs4
          · -- n < 447122302
            rcases Nat.lt_or_ge n 446942446 with hs5 | hs5
            · -- n < 446942446
              exact Brocard.berndt_galway_chunk_2485 n m (by omega) (by omega) h
            · -- n >= 446942446
              exact Brocard.berndt_galway_chunk_2486 n m (by omega) (by omega) h
          · -- n >= 447122302
            exact Brocard.berndt_galway_chunk_2487 n m (by omega) (by omega) h
      · -- n >= 447302158
        rcases Nat.lt_or_ge n 447841726 with hs3 | hs3
        · -- n < 447841726
          rcases Nat.lt_or_ge n 447661870 with hs4 | hs4
          · -- n < 447661870
            rcases Nat.lt_or_ge n 447482014 with hs5 | hs5
            · -- n < 447482014
              exact Brocard.berndt_galway_chunk_2488 n m (by omega) (by omega) h
            · -- n >= 447482014
              exact Brocard.berndt_galway_chunk_2489 n m (by omega) (by omega) h
          · -- n >= 447661870
            exact Brocard.berndt_galway_chunk_2490 n m (by omega) (by omega) h
        · -- n >= 447841726
          rcases Nat.lt_or_ge n 448201438 with hs4 | hs4
          · -- n < 448201438
            rcases Nat.lt_or_ge n 448021582 with hs5 | hs5
            · -- n < 448021582
              exact Brocard.berndt_galway_chunk_2491 n m (by omega) (by omega) h
            · -- n >= 448021582
              exact Brocard.berndt_galway_chunk_2492 n m (by omega) (by omega) h
          · -- n >= 448201438
            exact Brocard.berndt_galway_chunk_2493 n m (by omega) (by omega) h
    · -- n >= 448381294
      rcases Nat.lt_or_ge n 449460431 with hs2 | hs2
      · -- n < 449460431
        rcases Nat.lt_or_ge n 448920863 with hs3 | hs3
        · -- n < 448920863
          rcases Nat.lt_or_ge n 448741007 with hs4 | hs4
          · -- n < 448741007
            rcases Nat.lt_or_ge n 448561151 with hs5 | hs5
            · -- n < 448561151
              exact Brocard.berndt_galway_chunk_2494 n m (by omega) (by omega) h
            · -- n >= 448561151
              exact Brocard.berndt_galway_chunk_2495 n m (by omega) (by omega) h
          · -- n >= 448741007
            exact Brocard.berndt_galway_chunk_2496 n m (by omega) (by omega) h
        · -- n >= 448920863
          rcases Nat.lt_or_ge n 449280575 with hs4 | hs4
          · -- n < 449280575
            rcases Nat.lt_or_ge n 449100719 with hs5 | hs5
            · -- n < 449100719
              exact Brocard.berndt_galway_chunk_2497 n m (by omega) (by omega) h
            · -- n >= 449100719
              exact Brocard.berndt_galway_chunk_2498 n m (by omega) (by omega) h
          · -- n >= 449280575
            exact Brocard.berndt_galway_chunk_2499 n m (by omega) (by omega) h
      · -- n >= 449460431
        rcases Nat.lt_or_ge n 450000000 with hs3 | hs3
        · -- n < 450000000
          rcases Nat.lt_or_ge n 449820143 with hs4 | hs4
          · -- n < 449820143
            rcases Nat.lt_or_ge n 449640287 with hs5 | hs5
            · -- n < 449640287
              exact Brocard.berndt_galway_chunk_2500 n m (by omega) (by omega) h
            · -- n >= 449640287
              exact Brocard.berndt_galway_chunk_2501 n m (by omega) (by omega) h
          · -- n >= 449820143
            exact Brocard.berndt_galway_chunk_2502 n m (by omega) (by omega) h
        · -- n >= 450000000
          rcases Nat.lt_or_ge n 450179856 with hs4 | hs4
          · -- n < 450179856
            exact Brocard.berndt_galway_chunk_2503 n m (by omega) (by omega) h
          · -- n >= 450179856
            exact Brocard.berndt_galway_chunk_2504 n m (by omega) (by omega) h
