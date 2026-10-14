-- Prove2me | solution 1 for Brocard.berndt_galway_group_010
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:06:14.051408+00:00
-- url     : https://prove2.me/submissions/a88e084a-4d61-4f5a-a596-1d6498109349

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_0419
import Theorems.Thm_Brocard_berndt_galway_chunk_0420
import Theorems.Thm_Brocard_berndt_galway_chunk_0421
import Theorems.Thm_Brocard_berndt_galway_chunk_0422
import Theorems.Thm_Brocard_berndt_galway_chunk_0423
import Theorems.Thm_Brocard_berndt_galway_chunk_0424
import Theorems.Thm_Brocard_berndt_galway_chunk_0425
import Theorems.Thm_Brocard_berndt_galway_chunk_0426
import Theorems.Thm_Brocard_berndt_galway_chunk_0427
import Theorems.Thm_Brocard_berndt_galway_chunk_0428
import Theorems.Thm_Brocard_berndt_galway_chunk_0429
import Theorems.Thm_Brocard_berndt_galway_chunk_0430
import Theorems.Thm_Brocard_berndt_galway_chunk_0431
import Theorems.Thm_Brocard_berndt_galway_chunk_0432
import Theorems.Thm_Brocard_berndt_galway_chunk_0433
import Theorems.Thm_Brocard_berndt_galway_chunk_0434
import Theorems.Thm_Brocard_berndt_galway_chunk_0435
import Theorems.Thm_Brocard_berndt_galway_chunk_0436
import Theorems.Thm_Brocard_berndt_galway_chunk_0437
import Theorems.Thm_Brocard_berndt_galway_chunk_0438
import Theorems.Thm_Brocard_berndt_galway_chunk_0439
import Theorems.Thm_Brocard_berndt_galway_chunk_0440
import Theorems.Thm_Brocard_berndt_galway_chunk_0441
import Theorems.Thm_Brocard_berndt_galway_chunk_0442
import Theorems.Thm_Brocard_berndt_galway_chunk_0443
import Theorems.Thm_Brocard_berndt_galway_chunk_0444
import Theorems.Thm_Brocard_berndt_galway_chunk_0445
import Theorems.Thm_Brocard_berndt_galway_chunk_0446
import Theorems.Thm_Brocard_berndt_galway_chunk_0447
import Theorems.Thm_Brocard_berndt_galway_chunk_0448
import Theorems.Thm_Brocard_berndt_galway_chunk_0449
import Theorems.Thm_Brocard_berndt_galway_chunk_0450
import Theorems.Thm_Brocard_berndt_galway_chunk_0451
import Theorems.Thm_Brocard_berndt_galway_chunk_0452
import Theorems.Thm_Brocard_berndt_galway_chunk_0453
import Theorems.Thm_Brocard_berndt_galway_chunk_0454
import Theorems.Thm_Brocard_berndt_galway_chunk_0455
import Theorems.Thm_Brocard_berndt_galway_chunk_0456
import Theorems.Thm_Brocard_berndt_galway_chunk_0457
import Theorems.Thm_Brocard_berndt_galway_chunk_0458
import Theorems.Thm_Brocard_berndt_galway_chunk_0459
import Theorems.Thm_Brocard_berndt_galway_chunk_0460
import Theorems.Thm_Brocard_berndt_galway_chunk_0461
import Theorems.Thm_Brocard_berndt_galway_chunk_0462
import Theorems.Thm_Brocard_berndt_galway_chunk_0463
import Theorems.Thm_Brocard_berndt_galway_chunk_0464

theorem solution (n m : ℕ) (h1 : 75179858 ≤ n) (h2 : n < 83453238) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 79316548 with hs0 | hs0
  · -- n < 79316548
    rcases Nat.lt_or_ge n 77338131 with hs1 | hs1
    · -- n < 77338131
      rcases Nat.lt_or_ge n 76258994 with hs2 | hs2
      · -- n < 76258994
        rcases Nat.lt_or_ge n 75719426 with hs3 | hs3
        · -- n < 75719426
          rcases Nat.lt_or_ge n 75539570 with hs4 | hs4
          · -- n < 75539570
            rcases Nat.lt_or_ge n 75359714 with hs5 | hs5
            · -- n < 75359714
              exact Brocard.berndt_galway_chunk_0419 n m (by omega) (by omega) h
            · -- n >= 75359714
              exact Brocard.berndt_galway_chunk_0420 n m (by omega) (by omega) h
          · -- n >= 75539570
            exact Brocard.berndt_galway_chunk_0421 n m (by omega) (by omega) h
        · -- n >= 75719426
          rcases Nat.lt_or_ge n 76079138 with hs4 | hs4
          · -- n < 76079138
            rcases Nat.lt_or_ge n 75899282 with hs5 | hs5
            · -- n < 75899282
              exact Brocard.berndt_galway_chunk_0422 n m (by omega) (by omega) h
            · -- n >= 75899282
              exact Brocard.berndt_galway_chunk_0423 n m (by omega) (by omega) h
          · -- n >= 76079138
            exact Brocard.berndt_galway_chunk_0424 n m (by omega) (by omega) h
      · -- n >= 76258994
        rcases Nat.lt_or_ge n 76798563 with hs3 | hs3
        · -- n < 76798563
          rcases Nat.lt_or_ge n 76618706 with hs4 | hs4
          · -- n < 76618706
            rcases Nat.lt_or_ge n 76438850 with hs5 | hs5
            · -- n < 76438850
              exact Brocard.berndt_galway_chunk_0425 n m (by omega) (by omega) h
            · -- n >= 76438850
              exact Brocard.berndt_galway_chunk_0426 n m (by omega) (by omega) h
          · -- n >= 76618706
            exact Brocard.berndt_galway_chunk_0427 n m (by omega) (by omega) h
        · -- n >= 76798563
          rcases Nat.lt_or_ge n 77158275 with hs4 | hs4
          · -- n < 77158275
            rcases Nat.lt_or_ge n 76978419 with hs5 | hs5
            · -- n < 76978419
              exact Brocard.berndt_galway_chunk_0428 n m (by omega) (by omega) h
            · -- n >= 76978419
              exact Brocard.berndt_galway_chunk_0429 n m (by omega) (by omega) h
          · -- n >= 77158275
            exact Brocard.berndt_galway_chunk_0430 n m (by omega) (by omega) h
    · -- n >= 77338131
      rcases Nat.lt_or_ge n 78417267 with hs2 | hs2
      · -- n < 78417267
        rcases Nat.lt_or_ge n 77877699 with hs3 | hs3
        · -- n < 77877699
          rcases Nat.lt_or_ge n 77697843 with hs4 | hs4
          · -- n < 77697843
            rcases Nat.lt_or_ge n 77517987 with hs5 | hs5
            · -- n < 77517987
              exact Brocard.berndt_galway_chunk_0431 n m (by omega) (by omega) h
            · -- n >= 77517987
              exact Brocard.berndt_galway_chunk_0432 n m (by omega) (by omega) h
          · -- n >= 77697843
            exact Brocard.berndt_galway_chunk_0433 n m (by omega) (by omega) h
        · -- n >= 77877699
          rcases Nat.lt_or_ge n 78237411 with hs4 | hs4
          · -- n < 78237411
            rcases Nat.lt_or_ge n 78057555 with hs5 | hs5
            · -- n < 78057555
              exact Brocard.berndt_galway_chunk_0434 n m (by omega) (by omega) h
            · -- n >= 78057555
              exact Brocard.berndt_galway_chunk_0435 n m (by omega) (by omega) h
          · -- n >= 78237411
            exact Brocard.berndt_galway_chunk_0436 n m (by omega) (by omega) h
      · -- n >= 78417267
        rcases Nat.lt_or_ge n 78956836 with hs3 | hs3
        · -- n < 78956836
          rcases Nat.lt_or_ge n 78776980 with hs4 | hs4
          · -- n < 78776980
            rcases Nat.lt_or_ge n 78597124 with hs5 | hs5
            · -- n < 78597124
              exact Brocard.berndt_galway_chunk_0437 n m (by omega) (by omega) h
            · -- n >= 78597124
              exact Brocard.berndt_galway_chunk_0438 n m (by omega) (by omega) h
          · -- n >= 78776980
            exact Brocard.berndt_galway_chunk_0439 n m (by omega) (by omega) h
        · -- n >= 78956836
          rcases Nat.lt_or_ge n 79136692 with hs4 | hs4
          · -- n < 79136692
            exact Brocard.berndt_galway_chunk_0440 n m (by omega) (by omega) h
          · -- n >= 79136692
            exact Brocard.berndt_galway_chunk_0441 n m (by omega) (by omega) h
  · -- n >= 79316548
    rcases Nat.lt_or_ge n 81474821 with hs1 | hs1
    · -- n < 81474821
      rcases Nat.lt_or_ge n 80395685 with hs2 | hs2
      · -- n < 80395685
        rcases Nat.lt_or_ge n 79856116 with hs3 | hs3
        · -- n < 79856116
          rcases Nat.lt_or_ge n 79676260 with hs4 | hs4
          · -- n < 79676260
            rcases Nat.lt_or_ge n 79496404 with hs5 | hs5
            · -- n < 79496404
              exact Brocard.berndt_galway_chunk_0442 n m (by omega) (by omega) h
            · -- n >= 79496404
              exact Brocard.berndt_galway_chunk_0443 n m (by omega) (by omega) h
          · -- n >= 79676260
            exact Brocard.berndt_galway_chunk_0444 n m (by omega) (by omega) h
        · -- n >= 79856116
          rcases Nat.lt_or_ge n 80215828 with hs4 | hs4
          · -- n < 80215828
            rcases Nat.lt_or_ge n 80035972 with hs5 | hs5
            · -- n < 80035972
              exact Brocard.berndt_galway_chunk_0445 n m (by omega) (by omega) h
            · -- n >= 80035972
              exact Brocard.berndt_galway_chunk_0446 n m (by omega) (by omega) h
          · -- n >= 80215828
            exact Brocard.berndt_galway_chunk_0447 n m (by omega) (by omega) h
      · -- n >= 80395685
        rcases Nat.lt_or_ge n 80935253 with hs3 | hs3
        · -- n < 80935253
          rcases Nat.lt_or_ge n 80755397 with hs4 | hs4
          · -- n < 80755397
            rcases Nat.lt_or_ge n 80575541 with hs5 | hs5
            · -- n < 80575541
              exact Brocard.berndt_galway_chunk_0448 n m (by omega) (by omega) h
            · -- n >= 80575541
              exact Brocard.berndt_galway_chunk_0449 n m (by omega) (by omega) h
          · -- n >= 80755397
            exact Brocard.berndt_galway_chunk_0450 n m (by omega) (by omega) h
        · -- n >= 80935253
          rcases Nat.lt_or_ge n 81294965 with hs4 | hs4
          · -- n < 81294965
            rcases Nat.lt_or_ge n 81115109 with hs5 | hs5
            · -- n < 81115109
              exact Brocard.berndt_galway_chunk_0451 n m (by omega) (by omega) h
            · -- n >= 81115109
              exact Brocard.berndt_galway_chunk_0452 n m (by omega) (by omega) h
          · -- n >= 81294965
            exact Brocard.berndt_galway_chunk_0453 n m (by omega) (by omega) h
    · -- n >= 81474821
      rcases Nat.lt_or_ge n 82553958 with hs2 | hs2
      · -- n < 82553958
        rcases Nat.lt_or_ge n 82014389 with hs3 | hs3
        · -- n < 82014389
          rcases Nat.lt_or_ge n 81834533 with hs4 | hs4
          · -- n < 81834533
            rcases Nat.lt_or_ge n 81654677 with hs5 | hs5
            · -- n < 81654677
              exact Brocard.berndt_galway_chunk_0454 n m (by omega) (by omega) h
            · -- n >= 81654677
              exact Brocard.berndt_galway_chunk_0455 n m (by omega) (by omega) h
          · -- n >= 81834533
            exact Brocard.berndt_galway_chunk_0456 n m (by omega) (by omega) h
        · -- n >= 82014389
          rcases Nat.lt_or_ge n 82374102 with hs4 | hs4
          · -- n < 82374102
            rcases Nat.lt_or_ge n 82194246 with hs5 | hs5
            · -- n < 82194246
              exact Brocard.berndt_galway_chunk_0457 n m (by omega) (by omega) h
            · -- n >= 82194246
              exact Brocard.berndt_galway_chunk_0458 n m (by omega) (by omega) h
          · -- n >= 82374102
            exact Brocard.berndt_galway_chunk_0459 n m (by omega) (by omega) h
      · -- n >= 82553958
        rcases Nat.lt_or_ge n 83093526 with hs3 | hs3
        · -- n < 83093526
          rcases Nat.lt_or_ge n 82913670 with hs4 | hs4
          · -- n < 82913670
            rcases Nat.lt_or_ge n 82733814 with hs5 | hs5
            · -- n < 82733814
              exact Brocard.berndt_galway_chunk_0460 n m (by omega) (by omega) h
            · -- n >= 82733814
              exact Brocard.berndt_galway_chunk_0461 n m (by omega) (by omega) h
          · -- n >= 82913670
            exact Brocard.berndt_galway_chunk_0462 n m (by omega) (by omega) h
        · -- n >= 83093526
          rcases Nat.lt_or_ge n 83273382 with hs4 | hs4
          · -- n < 83273382
            exact Brocard.berndt_galway_chunk_0463 n m (by omega) (by omega) h
          · -- n >= 83273382
            exact Brocard.berndt_galway_chunk_0464 n m (by omega) (by omega) h
