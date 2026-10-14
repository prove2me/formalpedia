-- Prove2me | solution 1 for Brocard.berndt_galway_group_055
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:11:37.177996+00:00
-- url     : https://prove2.me/submissions/847c252a-7131-4250-8f3b-d2a60ab2aecf

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_2505
import Theorems.Thm_Brocard_berndt_galway_chunk_2506
import Theorems.Thm_Brocard_berndt_galway_chunk_2507
import Theorems.Thm_Brocard_berndt_galway_chunk_2508
import Theorems.Thm_Brocard_berndt_galway_chunk_2509
import Theorems.Thm_Brocard_berndt_galway_chunk_2510
import Theorems.Thm_Brocard_berndt_galway_chunk_2511
import Theorems.Thm_Brocard_berndt_galway_chunk_2512
import Theorems.Thm_Brocard_berndt_galway_chunk_2513
import Theorems.Thm_Brocard_berndt_galway_chunk_2514
import Theorems.Thm_Brocard_berndt_galway_chunk_2515
import Theorems.Thm_Brocard_berndt_galway_chunk_2516
import Theorems.Thm_Brocard_berndt_galway_chunk_2517
import Theorems.Thm_Brocard_berndt_galway_chunk_2518
import Theorems.Thm_Brocard_berndt_galway_chunk_2519
import Theorems.Thm_Brocard_berndt_galway_chunk_2520
import Theorems.Thm_Brocard_berndt_galway_chunk_2521
import Theorems.Thm_Brocard_berndt_galway_chunk_2522
import Theorems.Thm_Brocard_berndt_galway_chunk_2523
import Theorems.Thm_Brocard_berndt_galway_chunk_2524
import Theorems.Thm_Brocard_berndt_galway_chunk_2525
import Theorems.Thm_Brocard_berndt_galway_chunk_2526
import Theorems.Thm_Brocard_berndt_galway_chunk_2527
import Theorems.Thm_Brocard_berndt_galway_chunk_2528
import Theorems.Thm_Brocard_berndt_galway_chunk_2529
import Theorems.Thm_Brocard_berndt_galway_chunk_2530
import Theorems.Thm_Brocard_berndt_galway_chunk_2531
import Theorems.Thm_Brocard_berndt_galway_chunk_2532
import Theorems.Thm_Brocard_berndt_galway_chunk_2533
import Theorems.Thm_Brocard_berndt_galway_chunk_2534
import Theorems.Thm_Brocard_berndt_galway_chunk_2535
import Theorems.Thm_Brocard_berndt_galway_chunk_2536
import Theorems.Thm_Brocard_berndt_galway_chunk_2537
import Theorems.Thm_Brocard_berndt_galway_chunk_2538
import Theorems.Thm_Brocard_berndt_galway_chunk_2539
import Theorems.Thm_Brocard_berndt_galway_chunk_2540
import Theorems.Thm_Brocard_berndt_galway_chunk_2541
import Theorems.Thm_Brocard_berndt_galway_chunk_2542
import Theorems.Thm_Brocard_berndt_galway_chunk_2543
import Theorems.Thm_Brocard_berndt_galway_chunk_2544
import Theorems.Thm_Brocard_berndt_galway_chunk_2545
import Theorems.Thm_Brocard_berndt_galway_chunk_2546
import Theorems.Thm_Brocard_berndt_galway_chunk_2547
import Theorems.Thm_Brocard_berndt_galway_chunk_2548
import Theorems.Thm_Brocard_berndt_galway_chunk_2549
import Theorems.Thm_Brocard_berndt_galway_chunk_2550

theorem solution (n m : ℕ) (h1 : 450359712 ≤ n) (h2 : n < 458633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 454496402 with hs0 | hs0
  · -- n < 454496402
    rcases Nat.lt_or_ge n 452517985 with hs1 | hs1
    · -- n < 452517985
      rcases Nat.lt_or_ge n 451438848 with hs2 | hs2
      · -- n < 451438848
        rcases Nat.lt_or_ge n 450899280 with hs3 | hs3
        · -- n < 450899280
          rcases Nat.lt_or_ge n 450719424 with hs4 | hs4
          · -- n < 450719424
            rcases Nat.lt_or_ge n 450539568 with hs5 | hs5
            · -- n < 450539568
              exact Brocard.berndt_galway_chunk_2505 n m (by omega) (by omega) h
            · -- n >= 450539568
              exact Brocard.berndt_galway_chunk_2506 n m (by omega) (by omega) h
          · -- n >= 450719424
            exact Brocard.berndt_galway_chunk_2507 n m (by omega) (by omega) h
        · -- n >= 450899280
          rcases Nat.lt_or_ge n 451258992 with hs4 | hs4
          · -- n < 451258992
            rcases Nat.lt_or_ge n 451079136 with hs5 | hs5
            · -- n < 451079136
              exact Brocard.berndt_galway_chunk_2508 n m (by omega) (by omega) h
            · -- n >= 451079136
              exact Brocard.berndt_galway_chunk_2509 n m (by omega) (by omega) h
          · -- n >= 451258992
            exact Brocard.berndt_galway_chunk_2510 n m (by omega) (by omega) h
      · -- n >= 451438848
        rcases Nat.lt_or_ge n 451978417 with hs3 | hs3
        · -- n < 451978417
          rcases Nat.lt_or_ge n 451798561 with hs4 | hs4
          · -- n < 451798561
            rcases Nat.lt_or_ge n 451618705 with hs5 | hs5
            · -- n < 451618705
              exact Brocard.berndt_galway_chunk_2511 n m (by omega) (by omega) h
            · -- n >= 451618705
              exact Brocard.berndt_galway_chunk_2512 n m (by omega) (by omega) h
          · -- n >= 451798561
            exact Brocard.berndt_galway_chunk_2513 n m (by omega) (by omega) h
        · -- n >= 451978417
          rcases Nat.lt_or_ge n 452338129 with hs4 | hs4
          · -- n < 452338129
            rcases Nat.lt_or_ge n 452158273 with hs5 | hs5
            · -- n < 452158273
              exact Brocard.berndt_galway_chunk_2514 n m (by omega) (by omega) h
            · -- n >= 452158273
              exact Brocard.berndt_galway_chunk_2515 n m (by omega) (by omega) h
          · -- n >= 452338129
            exact Brocard.berndt_galway_chunk_2516 n m (by omega) (by omega) h
    · -- n >= 452517985
      rcases Nat.lt_or_ge n 453597122 with hs2 | hs2
      · -- n < 453597122
        rcases Nat.lt_or_ge n 453057553 with hs3 | hs3
        · -- n < 453057553
          rcases Nat.lt_or_ge n 452877697 with hs4 | hs4
          · -- n < 452877697
            rcases Nat.lt_or_ge n 452697841 with hs5 | hs5
            · -- n < 452697841
              exact Brocard.berndt_galway_chunk_2517 n m (by omega) (by omega) h
            · -- n >= 452697841
              exact Brocard.berndt_galway_chunk_2518 n m (by omega) (by omega) h
          · -- n >= 452877697
            exact Brocard.berndt_galway_chunk_2519 n m (by omega) (by omega) h
        · -- n >= 453057553
          rcases Nat.lt_or_ge n 453417266 with hs4 | hs4
          · -- n < 453417266
            rcases Nat.lt_or_ge n 453237410 with hs5 | hs5
            · -- n < 453237410
              exact Brocard.berndt_galway_chunk_2520 n m (by omega) (by omega) h
            · -- n >= 453237410
              exact Brocard.berndt_galway_chunk_2521 n m (by omega) (by omega) h
          · -- n >= 453417266
            exact Brocard.berndt_galway_chunk_2522 n m (by omega) (by omega) h
      · -- n >= 453597122
        rcases Nat.lt_or_ge n 454136690 with hs3 | hs3
        · -- n < 454136690
          rcases Nat.lt_or_ge n 453956834 with hs4 | hs4
          · -- n < 453956834
            rcases Nat.lt_or_ge n 453776978 with hs5 | hs5
            · -- n < 453776978
              exact Brocard.berndt_galway_chunk_2523 n m (by omega) (by omega) h
            · -- n >= 453776978
              exact Brocard.berndt_galway_chunk_2524 n m (by omega) (by omega) h
          · -- n >= 453956834
            exact Brocard.berndt_galway_chunk_2525 n m (by omega) (by omega) h
        · -- n >= 454136690
          rcases Nat.lt_or_ge n 454316546 with hs4 | hs4
          · -- n < 454316546
            exact Brocard.berndt_galway_chunk_2526 n m (by omega) (by omega) h
          · -- n >= 454316546
            exact Brocard.berndt_galway_chunk_2527 n m (by omega) (by omega) h
  · -- n >= 454496402
    rcases Nat.lt_or_ge n 456654676 with hs1 | hs1
    · -- n < 456654676
      rcases Nat.lt_or_ge n 455575539 with hs2 | hs2
      · -- n < 455575539
        rcases Nat.lt_or_ge n 455035971 with hs3 | hs3
        · -- n < 455035971
          rcases Nat.lt_or_ge n 454856115 with hs4 | hs4
          · -- n < 454856115
            rcases Nat.lt_or_ge n 454676258 with hs5 | hs5
            · -- n < 454676258
              exact Brocard.berndt_galway_chunk_2528 n m (by omega) (by omega) h
            · -- n >= 454676258
              exact Brocard.berndt_galway_chunk_2529 n m (by omega) (by omega) h
          · -- n >= 454856115
            exact Brocard.berndt_galway_chunk_2530 n m (by omega) (by omega) h
        · -- n >= 455035971
          rcases Nat.lt_or_ge n 455395683 with hs4 | hs4
          · -- n < 455395683
            rcases Nat.lt_or_ge n 455215827 with hs5 | hs5
            · -- n < 455215827
              exact Brocard.berndt_galway_chunk_2531 n m (by omega) (by omega) h
            · -- n >= 455215827
              exact Brocard.berndt_galway_chunk_2532 n m (by omega) (by omega) h
          · -- n >= 455395683
            exact Brocard.berndt_galway_chunk_2533 n m (by omega) (by omega) h
      · -- n >= 455575539
        rcases Nat.lt_or_ge n 456115107 with hs3 | hs3
        · -- n < 456115107
          rcases Nat.lt_or_ge n 455935251 with hs4 | hs4
          · -- n < 455935251
            rcases Nat.lt_or_ge n 455755395 with hs5 | hs5
            · -- n < 455755395
              exact Brocard.berndt_galway_chunk_2534 n m (by omega) (by omega) h
            · -- n >= 455755395
              exact Brocard.berndt_galway_chunk_2535 n m (by omega) (by omega) h
          · -- n >= 455935251
            exact Brocard.berndt_galway_chunk_2536 n m (by omega) (by omega) h
        · -- n >= 456115107
          rcases Nat.lt_or_ge n 456474820 with hs4 | hs4
          · -- n < 456474820
            rcases Nat.lt_or_ge n 456294964 with hs5 | hs5
            · -- n < 456294964
              exact Brocard.berndt_galway_chunk_2537 n m (by omega) (by omega) h
            · -- n >= 456294964
              exact Brocard.berndt_galway_chunk_2538 n m (by omega) (by omega) h
          · -- n >= 456474820
            exact Brocard.berndt_galway_chunk_2539 n m (by omega) (by omega) h
    · -- n >= 456654676
      rcases Nat.lt_or_ge n 457733812 with hs2 | hs2
      · -- n < 457733812
        rcases Nat.lt_or_ge n 457194244 with hs3 | hs3
        · -- n < 457194244
          rcases Nat.lt_or_ge n 457014388 with hs4 | hs4
          · -- n < 457014388
            rcases Nat.lt_or_ge n 456834532 with hs5 | hs5
            · -- n < 456834532
              exact Brocard.berndt_galway_chunk_2540 n m (by omega) (by omega) h
            · -- n >= 456834532
              exact Brocard.berndt_galway_chunk_2541 n m (by omega) (by omega) h
          · -- n >= 457014388
            exact Brocard.berndt_galway_chunk_2542 n m (by omega) (by omega) h
        · -- n >= 457194244
          rcases Nat.lt_or_ge n 457553956 with hs4 | hs4
          · -- n < 457553956
            rcases Nat.lt_or_ge n 457374100 with hs5 | hs5
            · -- n < 457374100
              exact Brocard.berndt_galway_chunk_2543 n m (by omega) (by omega) h
            · -- n >= 457374100
              exact Brocard.berndt_galway_chunk_2544 n m (by omega) (by omega) h
          · -- n >= 457553956
            exact Brocard.berndt_galway_chunk_2545 n m (by omega) (by omega) h
      · -- n >= 457733812
        rcases Nat.lt_or_ge n 458273381 with hs3 | hs3
        · -- n < 458273381
          rcases Nat.lt_or_ge n 458093525 with hs4 | hs4
          · -- n < 458093525
            rcases Nat.lt_or_ge n 457913669 with hs5 | hs5
            · -- n < 457913669
              exact Brocard.berndt_galway_chunk_2546 n m (by omega) (by omega) h
            · -- n >= 457913669
              exact Brocard.berndt_galway_chunk_2547 n m (by omega) (by omega) h
          · -- n >= 458093525
            exact Brocard.berndt_galway_chunk_2548 n m (by omega) (by omega) h
        · -- n >= 458273381
          rcases Nat.lt_or_ge n 458453237 with hs4 | hs4
          · -- n < 458453237
            exact Brocard.berndt_galway_chunk_2549 n m (by omega) (by omega) h
          · -- n >= 458453237
            exact Brocard.berndt_galway_chunk_2550 n m (by omega) (by omega) h
