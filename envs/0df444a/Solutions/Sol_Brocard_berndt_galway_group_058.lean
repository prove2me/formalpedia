-- Prove2me | solution 1 for Brocard.berndt_galway_group_058
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:33:50.997986+00:00
-- url     : https://prove2.me/submissions/6dd40127-015b-45a0-9dc2-59fb39323dc4

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_2643
import Theorems.Thm_Brocard_berndt_galway_chunk_2644
import Theorems.Thm_Brocard_berndt_galway_chunk_2645
import Theorems.Thm_Brocard_berndt_galway_chunk_2646
import Theorems.Thm_Brocard_berndt_galway_chunk_2647
import Theorems.Thm_Brocard_berndt_galway_chunk_2648
import Theorems.Thm_Brocard_berndt_galway_chunk_2649
import Theorems.Thm_Brocard_berndt_galway_chunk_2650
import Theorems.Thm_Brocard_berndt_galway_chunk_2651
import Theorems.Thm_Brocard_berndt_galway_chunk_2652
import Theorems.Thm_Brocard_berndt_galway_chunk_2653
import Theorems.Thm_Brocard_berndt_galway_chunk_2654
import Theorems.Thm_Brocard_berndt_galway_chunk_2655
import Theorems.Thm_Brocard_berndt_galway_chunk_2656
import Theorems.Thm_Brocard_berndt_galway_chunk_2657
import Theorems.Thm_Brocard_berndt_galway_chunk_2658
import Theorems.Thm_Brocard_berndt_galway_chunk_2659
import Theorems.Thm_Brocard_berndt_galway_chunk_2660
import Theorems.Thm_Brocard_berndt_galway_chunk_2661
import Theorems.Thm_Brocard_berndt_galway_chunk_2662
import Theorems.Thm_Brocard_berndt_galway_chunk_2663
import Theorems.Thm_Brocard_berndt_galway_chunk_2664
import Theorems.Thm_Brocard_berndt_galway_chunk_2665
import Theorems.Thm_Brocard_berndt_galway_chunk_2666
import Theorems.Thm_Brocard_berndt_galway_chunk_2667
import Theorems.Thm_Brocard_berndt_galway_chunk_2668
import Theorems.Thm_Brocard_berndt_galway_chunk_2669
import Theorems.Thm_Brocard_berndt_galway_chunk_2670
import Theorems.Thm_Brocard_berndt_galway_chunk_2671
import Theorems.Thm_Brocard_berndt_galway_chunk_2672
import Theorems.Thm_Brocard_berndt_galway_chunk_2673
import Theorems.Thm_Brocard_berndt_galway_chunk_2674
import Theorems.Thm_Brocard_berndt_galway_chunk_2675
import Theorems.Thm_Brocard_berndt_galway_chunk_2676
import Theorems.Thm_Brocard_berndt_galway_chunk_2677
import Theorems.Thm_Brocard_berndt_galway_chunk_2678
import Theorems.Thm_Brocard_berndt_galway_chunk_2679
import Theorems.Thm_Brocard_berndt_galway_chunk_2680
import Theorems.Thm_Brocard_berndt_galway_chunk_2681
import Theorems.Thm_Brocard_berndt_galway_chunk_2682
import Theorems.Thm_Brocard_berndt_galway_chunk_2683
import Theorems.Thm_Brocard_berndt_galway_chunk_2684
import Theorems.Thm_Brocard_berndt_galway_chunk_2685
import Theorems.Thm_Brocard_berndt_galway_chunk_2686
import Theorems.Thm_Brocard_berndt_galway_chunk_2687
import Theorems.Thm_Brocard_berndt_galway_chunk_2688

theorem solution (n m : ℕ) (h1 : 475179856 ≤ n) (h2 : n < 483453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 479316546 with hs0 | hs0
  · -- n < 479316546
    rcases Nat.lt_or_ge n 477338129 with hs1 | hs1
    · -- n < 477338129
      rcases Nat.lt_or_ge n 476258992 with hs2 | hs2
      · -- n < 476258992
        rcases Nat.lt_or_ge n 475719424 with hs3 | hs3
        · -- n < 475719424
          rcases Nat.lt_or_ge n 475539568 with hs4 | hs4
          · -- n < 475539568
            rcases Nat.lt_or_ge n 475359712 with hs5 | hs5
            · -- n < 475359712
              exact Brocard.berndt_galway_chunk_2643 n m (by omega) (by omega) h
            · -- n >= 475359712
              exact Brocard.berndt_galway_chunk_2644 n m (by omega) (by omega) h
          · -- n >= 475539568
            exact Brocard.berndt_galway_chunk_2645 n m (by omega) (by omega) h
        · -- n >= 475719424
          rcases Nat.lt_or_ge n 476079136 with hs4 | hs4
          · -- n < 476079136
            rcases Nat.lt_or_ge n 475899280 with hs5 | hs5
            · -- n < 475899280
              exact Brocard.berndt_galway_chunk_2646 n m (by omega) (by omega) h
            · -- n >= 475899280
              exact Brocard.berndt_galway_chunk_2647 n m (by omega) (by omega) h
          · -- n >= 476079136
            exact Brocard.berndt_galway_chunk_2648 n m (by omega) (by omega) h
      · -- n >= 476258992
        rcases Nat.lt_or_ge n 476798561 with hs3 | hs3
        · -- n < 476798561
          rcases Nat.lt_or_ge n 476618705 with hs4 | hs4
          · -- n < 476618705
            rcases Nat.lt_or_ge n 476438848 with hs5 | hs5
            · -- n < 476438848
              exact Brocard.berndt_galway_chunk_2649 n m (by omega) (by omega) h
            · -- n >= 476438848
              exact Brocard.berndt_galway_chunk_2650 n m (by omega) (by omega) h
          · -- n >= 476618705
            exact Brocard.berndt_galway_chunk_2651 n m (by omega) (by omega) h
        · -- n >= 476798561
          rcases Nat.lt_or_ge n 477158273 with hs4 | hs4
          · -- n < 477158273
            rcases Nat.lt_or_ge n 476978417 with hs5 | hs5
            · -- n < 476978417
              exact Brocard.berndt_galway_chunk_2652 n m (by omega) (by omega) h
            · -- n >= 476978417
              exact Brocard.berndt_galway_chunk_2653 n m (by omega) (by omega) h
          · -- n >= 477158273
            exact Brocard.berndt_galway_chunk_2654 n m (by omega) (by omega) h
    · -- n >= 477338129
      rcases Nat.lt_or_ge n 478417266 with hs2 | hs2
      · -- n < 478417266
        rcases Nat.lt_or_ge n 477877697 with hs3 | hs3
        · -- n < 477877697
          rcases Nat.lt_or_ge n 477697841 with hs4 | hs4
          · -- n < 477697841
            rcases Nat.lt_or_ge n 477517985 with hs5 | hs5
            · -- n < 477517985
              exact Brocard.berndt_galway_chunk_2655 n m (by omega) (by omega) h
            · -- n >= 477517985
              exact Brocard.berndt_galway_chunk_2656 n m (by omega) (by omega) h
          · -- n >= 477697841
            exact Brocard.berndt_galway_chunk_2657 n m (by omega) (by omega) h
        · -- n >= 477877697
          rcases Nat.lt_or_ge n 478237410 with hs4 | hs4
          · -- n < 478237410
            rcases Nat.lt_or_ge n 478057553 with hs5 | hs5
            · -- n < 478057553
              exact Brocard.berndt_galway_chunk_2658 n m (by omega) (by omega) h
            · -- n >= 478057553
              exact Brocard.berndt_galway_chunk_2659 n m (by omega) (by omega) h
          · -- n >= 478237410
            exact Brocard.berndt_galway_chunk_2660 n m (by omega) (by omega) h
      · -- n >= 478417266
        rcases Nat.lt_or_ge n 478956834 with hs3 | hs3
        · -- n < 478956834
          rcases Nat.lt_or_ge n 478776978 with hs4 | hs4
          · -- n < 478776978
            rcases Nat.lt_or_ge n 478597122 with hs5 | hs5
            · -- n < 478597122
              exact Brocard.berndt_galway_chunk_2661 n m (by omega) (by omega) h
            · -- n >= 478597122
              exact Brocard.berndt_galway_chunk_2662 n m (by omega) (by omega) h
          · -- n >= 478776978
            exact Brocard.berndt_galway_chunk_2663 n m (by omega) (by omega) h
        · -- n >= 478956834
          rcases Nat.lt_or_ge n 479136690 with hs4 | hs4
          · -- n < 479136690
            exact Brocard.berndt_galway_chunk_2664 n m (by omega) (by omega) h
          · -- n >= 479136690
            exact Brocard.berndt_galway_chunk_2665 n m (by omega) (by omega) h
  · -- n >= 479316546
    rcases Nat.lt_or_ge n 481474820 with hs1 | hs1
    · -- n < 481474820
      rcases Nat.lt_or_ge n 480395683 with hs2 | hs2
      · -- n < 480395683
        rcases Nat.lt_or_ge n 479856115 with hs3 | hs3
        · -- n < 479856115
          rcases Nat.lt_or_ge n 479676258 with hs4 | hs4
          · -- n < 479676258
            rcases Nat.lt_or_ge n 479496402 with hs5 | hs5
            · -- n < 479496402
              exact Brocard.berndt_galway_chunk_2666 n m (by omega) (by omega) h
            · -- n >= 479496402
              exact Brocard.berndt_galway_chunk_2667 n m (by omega) (by omega) h
          · -- n >= 479676258
            exact Brocard.berndt_galway_chunk_2668 n m (by omega) (by omega) h
        · -- n >= 479856115
          rcases Nat.lt_or_ge n 480215827 with hs4 | hs4
          · -- n < 480215827
            rcases Nat.lt_or_ge n 480035971 with hs5 | hs5
            · -- n < 480035971
              exact Brocard.berndt_galway_chunk_2669 n m (by omega) (by omega) h
            · -- n >= 480035971
              exact Brocard.berndt_galway_chunk_2670 n m (by omega) (by omega) h
          · -- n >= 480215827
            exact Brocard.berndt_galway_chunk_2671 n m (by omega) (by omega) h
      · -- n >= 480395683
        rcases Nat.lt_or_ge n 480935251 with hs3 | hs3
        · -- n < 480935251
          rcases Nat.lt_or_ge n 480755395 with hs4 | hs4
          · -- n < 480755395
            rcases Nat.lt_or_ge n 480575539 with hs5 | hs5
            · -- n < 480575539
              exact Brocard.berndt_galway_chunk_2672 n m (by omega) (by omega) h
            · -- n >= 480575539
              exact Brocard.berndt_galway_chunk_2673 n m (by omega) (by omega) h
          · -- n >= 480755395
            exact Brocard.berndt_galway_chunk_2674 n m (by omega) (by omega) h
        · -- n >= 480935251
          rcases Nat.lt_or_ge n 481294964 with hs4 | hs4
          · -- n < 481294964
            rcases Nat.lt_or_ge n 481115107 with hs5 | hs5
            · -- n < 481115107
              exact Brocard.berndt_galway_chunk_2675 n m (by omega) (by omega) h
            · -- n >= 481115107
              exact Brocard.berndt_galway_chunk_2676 n m (by omega) (by omega) h
          · -- n >= 481294964
            exact Brocard.berndt_galway_chunk_2677 n m (by omega) (by omega) h
    · -- n >= 481474820
      rcases Nat.lt_or_ge n 482553956 with hs2 | hs2
      · -- n < 482553956
        rcases Nat.lt_or_ge n 482014388 with hs3 | hs3
        · -- n < 482014388
          rcases Nat.lt_or_ge n 481834532 with hs4 | hs4
          · -- n < 481834532
            rcases Nat.lt_or_ge n 481654676 with hs5 | hs5
            · -- n < 481654676
              exact Brocard.berndt_galway_chunk_2678 n m (by omega) (by omega) h
            · -- n >= 481654676
              exact Brocard.berndt_galway_chunk_2679 n m (by omega) (by omega) h
          · -- n >= 481834532
            exact Brocard.berndt_galway_chunk_2680 n m (by omega) (by omega) h
        · -- n >= 482014388
          rcases Nat.lt_or_ge n 482374100 with hs4 | hs4
          · -- n < 482374100
            rcases Nat.lt_or_ge n 482194244 with hs5 | hs5
            · -- n < 482194244
              exact Brocard.berndt_galway_chunk_2681 n m (by omega) (by omega) h
            · -- n >= 482194244
              exact Brocard.berndt_galway_chunk_2682 n m (by omega) (by omega) h
          · -- n >= 482374100
            exact Brocard.berndt_galway_chunk_2683 n m (by omega) (by omega) h
      · -- n >= 482553956
        rcases Nat.lt_or_ge n 483093525 with hs3 | hs3
        · -- n < 483093525
          rcases Nat.lt_or_ge n 482913669 with hs4 | hs4
          · -- n < 482913669
            rcases Nat.lt_or_ge n 482733812 with hs5 | hs5
            · -- n < 482733812
              exact Brocard.berndt_galway_chunk_2684 n m (by omega) (by omega) h
            · -- n >= 482733812
              exact Brocard.berndt_galway_chunk_2685 n m (by omega) (by omega) h
          · -- n >= 482913669
            exact Brocard.berndt_galway_chunk_2686 n m (by omega) (by omega) h
        · -- n >= 483093525
          rcases Nat.lt_or_ge n 483273381 with hs4 | hs4
          · -- n < 483273381
            exact Brocard.berndt_galway_chunk_2687 n m (by omega) (by omega) h
          · -- n >= 483273381
            exact Brocard.berndt_galway_chunk_2688 n m (by omega) (by omega) h
