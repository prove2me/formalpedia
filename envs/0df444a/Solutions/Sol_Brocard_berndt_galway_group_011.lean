-- Prove2me | solution 1 for Brocard.berndt_galway_group_011
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:21:39.711625+00:00
-- url     : https://prove2.me/submissions/74a3f36b-d6ea-4462-baa7-5e8bdd63f19c

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_0465
import Theorems.Thm_Brocard_berndt_galway_chunk_0466
import Theorems.Thm_Brocard_berndt_galway_chunk_0467
import Theorems.Thm_Brocard_berndt_galway_chunk_0468
import Theorems.Thm_Brocard_berndt_galway_chunk_0469
import Theorems.Thm_Brocard_berndt_galway_chunk_0470
import Theorems.Thm_Brocard_berndt_galway_chunk_0471
import Theorems.Thm_Brocard_berndt_galway_chunk_0472
import Theorems.Thm_Brocard_berndt_galway_chunk_0473
import Theorems.Thm_Brocard_berndt_galway_chunk_0474
import Theorems.Thm_Brocard_berndt_galway_chunk_0475
import Theorems.Thm_Brocard_berndt_galway_chunk_0476
import Theorems.Thm_Brocard_berndt_galway_chunk_0477
import Theorems.Thm_Brocard_berndt_galway_chunk_0478
import Theorems.Thm_Brocard_berndt_galway_chunk_0479
import Theorems.Thm_Brocard_berndt_galway_chunk_0480
import Theorems.Thm_Brocard_berndt_galway_chunk_0481
import Theorems.Thm_Brocard_berndt_galway_chunk_0482
import Theorems.Thm_Brocard_berndt_galway_chunk_0483
import Theorems.Thm_Brocard_berndt_galway_chunk_0484
import Theorems.Thm_Brocard_berndt_galway_chunk_0485
import Theorems.Thm_Brocard_berndt_galway_chunk_0486
import Theorems.Thm_Brocard_berndt_galway_chunk_0487
import Theorems.Thm_Brocard_berndt_galway_chunk_0488
import Theorems.Thm_Brocard_berndt_galway_chunk_0489
import Theorems.Thm_Brocard_berndt_galway_chunk_0490
import Theorems.Thm_Brocard_berndt_galway_chunk_0491
import Theorems.Thm_Brocard_berndt_galway_chunk_0492
import Theorems.Thm_Brocard_berndt_galway_chunk_0493
import Theorems.Thm_Brocard_berndt_galway_chunk_0494
import Theorems.Thm_Brocard_berndt_galway_chunk_0495
import Theorems.Thm_Brocard_berndt_galway_chunk_0496
import Theorems.Thm_Brocard_berndt_galway_chunk_0497
import Theorems.Thm_Brocard_berndt_galway_chunk_0498
import Theorems.Thm_Brocard_berndt_galway_chunk_0499
import Theorems.Thm_Brocard_berndt_galway_chunk_0500
import Theorems.Thm_Brocard_berndt_galway_chunk_0501
import Theorems.Thm_Brocard_berndt_galway_chunk_0502
import Theorems.Thm_Brocard_berndt_galway_chunk_0503
import Theorems.Thm_Brocard_berndt_galway_chunk_0504
import Theorems.Thm_Brocard_berndt_galway_chunk_0505
import Theorems.Thm_Brocard_berndt_galway_chunk_0506
import Theorems.Thm_Brocard_berndt_galway_chunk_0507
import Theorems.Thm_Brocard_berndt_galway_chunk_0508
import Theorems.Thm_Brocard_berndt_galway_chunk_0509
import Theorems.Thm_Brocard_berndt_galway_chunk_0510

theorem solution (n m : ℕ) (h1 : 83453238 ≤ n) (h2 : n < 91726619) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 87589929 with hs0 | hs0
  · -- n < 87589929
    rcases Nat.lt_or_ge n 85611511 with hs1 | hs1
    · -- n < 85611511
      rcases Nat.lt_or_ge n 84532375 with hs2 | hs2
      · -- n < 84532375
        rcases Nat.lt_or_ge n 83992807 with hs3 | hs3
        · -- n < 83992807
          rcases Nat.lt_or_ge n 83812950 with hs4 | hs4
          · -- n < 83812950
            rcases Nat.lt_or_ge n 83633094 with hs5 | hs5
            · -- n < 83633094
              exact Brocard.berndt_galway_chunk_0465 n m (by omega) (by omega) h
            · -- n >= 83633094
              exact Brocard.berndt_galway_chunk_0466 n m (by omega) (by omega) h
          · -- n >= 83812950
            exact Brocard.berndt_galway_chunk_0467 n m (by omega) (by omega) h
        · -- n >= 83992807
          rcases Nat.lt_or_ge n 84352519 with hs4 | hs4
          · -- n < 84352519
            rcases Nat.lt_or_ge n 84172663 with hs5 | hs5
            · -- n < 84172663
              exact Brocard.berndt_galway_chunk_0468 n m (by omega) (by omega) h
            · -- n >= 84172663
              exact Brocard.berndt_galway_chunk_0469 n m (by omega) (by omega) h
          · -- n >= 84352519
            exact Brocard.berndt_galway_chunk_0470 n m (by omega) (by omega) h
      · -- n >= 84532375
        rcases Nat.lt_or_ge n 85071943 with hs3 | hs3
        · -- n < 85071943
          rcases Nat.lt_or_ge n 84892087 with hs4 | hs4
          · -- n < 84892087
            rcases Nat.lt_or_ge n 84712231 with hs5 | hs5
            · -- n < 84712231
              exact Brocard.berndt_galway_chunk_0471 n m (by omega) (by omega) h
            · -- n >= 84712231
              exact Brocard.berndt_galway_chunk_0472 n m (by omega) (by omega) h
          · -- n >= 84892087
            exact Brocard.berndt_galway_chunk_0473 n m (by omega) (by omega) h
        · -- n >= 85071943
          rcases Nat.lt_or_ge n 85431655 with hs4 | hs4
          · -- n < 85431655
            rcases Nat.lt_or_ge n 85251799 with hs5 | hs5
            · -- n < 85251799
              exact Brocard.berndt_galway_chunk_0474 n m (by omega) (by omega) h
            · -- n >= 85251799
              exact Brocard.berndt_galway_chunk_0475 n m (by omega) (by omega) h
          · -- n >= 85431655
            exact Brocard.berndt_galway_chunk_0476 n m (by omega) (by omega) h
    · -- n >= 85611511
      rcases Nat.lt_or_ge n 86690648 with hs2 | hs2
      · -- n < 86690648
        rcases Nat.lt_or_ge n 86151080 with hs3 | hs3
        · -- n < 86151080
          rcases Nat.lt_or_ge n 85971224 with hs4 | hs4
          · -- n < 85971224
            rcases Nat.lt_or_ge n 85791368 with hs5 | hs5
            · -- n < 85791368
              exact Brocard.berndt_galway_chunk_0477 n m (by omega) (by omega) h
            · -- n >= 85791368
              exact Brocard.berndt_galway_chunk_0478 n m (by omega) (by omega) h
          · -- n >= 85971224
            exact Brocard.berndt_galway_chunk_0479 n m (by omega) (by omega) h
        · -- n >= 86151080
          rcases Nat.lt_or_ge n 86510792 with hs4 | hs4
          · -- n < 86510792
            rcases Nat.lt_or_ge n 86330936 with hs5 | hs5
            · -- n < 86330936
              exact Brocard.berndt_galway_chunk_0480 n m (by omega) (by omega) h
            · -- n >= 86330936
              exact Brocard.berndt_galway_chunk_0481 n m (by omega) (by omega) h
          · -- n >= 86510792
            exact Brocard.berndt_galway_chunk_0482 n m (by omega) (by omega) h
      · -- n >= 86690648
        rcases Nat.lt_or_ge n 87230216 with hs3 | hs3
        · -- n < 87230216
          rcases Nat.lt_or_ge n 87050360 with hs4 | hs4
          · -- n < 87050360
            rcases Nat.lt_or_ge n 86870504 with hs5 | hs5
            · -- n < 86870504
              exact Brocard.berndt_galway_chunk_0483 n m (by omega) (by omega) h
            · -- n >= 86870504
              exact Brocard.berndt_galway_chunk_0484 n m (by omega) (by omega) h
          · -- n >= 87050360
            exact Brocard.berndt_galway_chunk_0485 n m (by omega) (by omega) h
        · -- n >= 87230216
          rcases Nat.lt_or_ge n 87410072 with hs4 | hs4
          · -- n < 87410072
            exact Brocard.berndt_galway_chunk_0486 n m (by omega) (by omega) h
          · -- n >= 87410072
            exact Brocard.berndt_galway_chunk_0487 n m (by omega) (by omega) h
  · -- n >= 87589929
    rcases Nat.lt_or_ge n 89748202 with hs1 | hs1
    · -- n < 89748202
      rcases Nat.lt_or_ge n 88669065 with hs2 | hs2
      · -- n < 88669065
        rcases Nat.lt_or_ge n 88129497 with hs3 | hs3
        · -- n < 88129497
          rcases Nat.lt_or_ge n 87949641 with hs4 | hs4
          · -- n < 87949641
            rcases Nat.lt_or_ge n 87769785 with hs5 | hs5
            · -- n < 87769785
              exact Brocard.berndt_galway_chunk_0488 n m (by omega) (by omega) h
            · -- n >= 87769785
              exact Brocard.berndt_galway_chunk_0489 n m (by omega) (by omega) h
          · -- n >= 87949641
            exact Brocard.berndt_galway_chunk_0490 n m (by omega) (by omega) h
        · -- n >= 88129497
          rcases Nat.lt_or_ge n 88489209 with hs4 | hs4
          · -- n < 88489209
            rcases Nat.lt_or_ge n 88309353 with hs5 | hs5
            · -- n < 88309353
              exact Brocard.berndt_galway_chunk_0491 n m (by omega) (by omega) h
            · -- n >= 88309353
              exact Brocard.berndt_galway_chunk_0492 n m (by omega) (by omega) h
          · -- n >= 88489209
            exact Brocard.berndt_galway_chunk_0493 n m (by omega) (by omega) h
      · -- n >= 88669065
        rcases Nat.lt_or_ge n 89208633 with hs3 | hs3
        · -- n < 89208633
          rcases Nat.lt_or_ge n 89028777 with hs4 | hs4
          · -- n < 89028777
            rcases Nat.lt_or_ge n 88848921 with hs5 | hs5
            · -- n < 88848921
              exact Brocard.berndt_galway_chunk_0494 n m (by omega) (by omega) h
            · -- n >= 88848921
              exact Brocard.berndt_galway_chunk_0495 n m (by omega) (by omega) h
          · -- n >= 89028777
            exact Brocard.berndt_galway_chunk_0496 n m (by omega) (by omega) h
        · -- n >= 89208633
          rcases Nat.lt_or_ge n 89568346 with hs4 | hs4
          · -- n < 89568346
            rcases Nat.lt_or_ge n 89388490 with hs5 | hs5
            · -- n < 89388490
              exact Brocard.berndt_galway_chunk_0497 n m (by omega) (by omega) h
            · -- n >= 89388490
              exact Brocard.berndt_galway_chunk_0498 n m (by omega) (by omega) h
          · -- n >= 89568346
            exact Brocard.berndt_galway_chunk_0499 n m (by omega) (by omega) h
    · -- n >= 89748202
      rcases Nat.lt_or_ge n 90827338 with hs2 | hs2
      · -- n < 90827338
        rcases Nat.lt_or_ge n 90287770 with hs3 | hs3
        · -- n < 90287770
          rcases Nat.lt_or_ge n 90107914 with hs4 | hs4
          · -- n < 90107914
            rcases Nat.lt_or_ge n 89928058 with hs5 | hs5
            · -- n < 89928058
              exact Brocard.berndt_galway_chunk_0500 n m (by omega) (by omega) h
            · -- n >= 89928058
              exact Brocard.berndt_galway_chunk_0501 n m (by omega) (by omega) h
          · -- n >= 90107914
            exact Brocard.berndt_galway_chunk_0502 n m (by omega) (by omega) h
        · -- n >= 90287770
          rcases Nat.lt_or_ge n 90647482 with hs4 | hs4
          · -- n < 90647482
            rcases Nat.lt_or_ge n 90467626 with hs5 | hs5
            · -- n < 90467626
              exact Brocard.berndt_galway_chunk_0503 n m (by omega) (by omega) h
            · -- n >= 90467626
              exact Brocard.berndt_galway_chunk_0504 n m (by omega) (by omega) h
          · -- n >= 90647482
            exact Brocard.berndt_galway_chunk_0505 n m (by omega) (by omega) h
      · -- n >= 90827338
        rcases Nat.lt_or_ge n 91366907 with hs3 | hs3
        · -- n < 91366907
          rcases Nat.lt_or_ge n 91187051 with hs4 | hs4
          · -- n < 91187051
            rcases Nat.lt_or_ge n 91007194 with hs5 | hs5
            · -- n < 91007194
              exact Brocard.berndt_galway_chunk_0506 n m (by omega) (by omega) h
            · -- n >= 91007194
              exact Brocard.berndt_galway_chunk_0507 n m (by omega) (by omega) h
          · -- n >= 91187051
            exact Brocard.berndt_galway_chunk_0508 n m (by omega) (by omega) h
        · -- n >= 91366907
          rcases Nat.lt_or_ge n 91546763 with hs4 | hs4
          · -- n < 91546763
            exact Brocard.berndt_galway_chunk_0509 n m (by omega) (by omega) h
          · -- n >= 91546763
            exact Brocard.berndt_galway_chunk_0510 n m (by omega) (by omega) h
