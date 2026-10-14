-- Prove2me | solution 1 for Brocard.berndt_galway_group_079
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:27:59.36844+00:00
-- url     : https://prove2.me/submissions/e9434feb-ac45-4f8c-9c2b-41b5ea0fddee

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_3617
import Theorems.Thm_Brocard_berndt_galway_chunk_3618
import Theorems.Thm_Brocard_berndt_galway_chunk_3619
import Theorems.Thm_Brocard_berndt_galway_chunk_3620
import Theorems.Thm_Brocard_berndt_galway_chunk_3621
import Theorems.Thm_Brocard_berndt_galway_chunk_3622
import Theorems.Thm_Brocard_berndt_galway_chunk_3623
import Theorems.Thm_Brocard_berndt_galway_chunk_3624
import Theorems.Thm_Brocard_berndt_galway_chunk_3625
import Theorems.Thm_Brocard_berndt_galway_chunk_3626
import Theorems.Thm_Brocard_berndt_galway_chunk_3627
import Theorems.Thm_Brocard_berndt_galway_chunk_3628
import Theorems.Thm_Brocard_berndt_galway_chunk_3629
import Theorems.Thm_Brocard_berndt_galway_chunk_3630
import Theorems.Thm_Brocard_berndt_galway_chunk_3631
import Theorems.Thm_Brocard_berndt_galway_chunk_3632
import Theorems.Thm_Brocard_berndt_galway_chunk_3633
import Theorems.Thm_Brocard_berndt_galway_chunk_3634
import Theorems.Thm_Brocard_berndt_galway_chunk_3635
import Theorems.Thm_Brocard_berndt_galway_chunk_3636
import Theorems.Thm_Brocard_berndt_galway_chunk_3637
import Theorems.Thm_Brocard_berndt_galway_chunk_3638
import Theorems.Thm_Brocard_berndt_galway_chunk_3639
import Theorems.Thm_Brocard_berndt_galway_chunk_3640
import Theorems.Thm_Brocard_berndt_galway_chunk_3641
import Theorems.Thm_Brocard_berndt_galway_chunk_3642
import Theorems.Thm_Brocard_berndt_galway_chunk_3643
import Theorems.Thm_Brocard_berndt_galway_chunk_3644
import Theorems.Thm_Brocard_berndt_galway_chunk_3645
import Theorems.Thm_Brocard_berndt_galway_chunk_3646
import Theorems.Thm_Brocard_berndt_galway_chunk_3647
import Theorems.Thm_Brocard_berndt_galway_chunk_3648
import Theorems.Thm_Brocard_berndt_galway_chunk_3649
import Theorems.Thm_Brocard_berndt_galway_chunk_3650
import Theorems.Thm_Brocard_berndt_galway_chunk_3651
import Theorems.Thm_Brocard_berndt_galway_chunk_3652
import Theorems.Thm_Brocard_berndt_galway_chunk_3653
import Theorems.Thm_Brocard_berndt_galway_chunk_3654
import Theorems.Thm_Brocard_berndt_galway_chunk_3655
import Theorems.Thm_Brocard_berndt_galway_chunk_3656
import Theorems.Thm_Brocard_berndt_galway_chunk_3657
import Theorems.Thm_Brocard_berndt_galway_chunk_3658
import Theorems.Thm_Brocard_berndt_galway_chunk_3659
import Theorems.Thm_Brocard_berndt_galway_chunk_3660
import Theorems.Thm_Brocard_berndt_galway_chunk_3661
import Theorems.Thm_Brocard_berndt_galway_chunk_3662

theorem solution (n m : ℕ) (h1 : 650359712 ≤ n) (h2 : n < 658633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 654496402 with hs0 | hs0
  · -- n < 654496402
    rcases Nat.lt_or_ge n 652517985 with hs1 | hs1
    · -- n < 652517985
      rcases Nat.lt_or_ge n 651438848 with hs2 | hs2
      · -- n < 651438848
        rcases Nat.lt_or_ge n 650899280 with hs3 | hs3
        · -- n < 650899280
          rcases Nat.lt_or_ge n 650719424 with hs4 | hs4
          · -- n < 650719424
            rcases Nat.lt_or_ge n 650539568 with hs5 | hs5
            · -- n < 650539568
              exact Brocard.berndt_galway_chunk_3617 n m (by omega) (by omega) h
            · -- n >= 650539568
              exact Brocard.berndt_galway_chunk_3618 n m (by omega) (by omega) h
          · -- n >= 650719424
            exact Brocard.berndt_galway_chunk_3619 n m (by omega) (by omega) h
        · -- n >= 650899280
          rcases Nat.lt_or_ge n 651258992 with hs4 | hs4
          · -- n < 651258992
            rcases Nat.lt_or_ge n 651079136 with hs5 | hs5
            · -- n < 651079136
              exact Brocard.berndt_galway_chunk_3620 n m (by omega) (by omega) h
            · -- n >= 651079136
              exact Brocard.berndt_galway_chunk_3621 n m (by omega) (by omega) h
          · -- n >= 651258992
            exact Brocard.berndt_galway_chunk_3622 n m (by omega) (by omega) h
      · -- n >= 651438848
        rcases Nat.lt_or_ge n 651978417 with hs3 | hs3
        · -- n < 651978417
          rcases Nat.lt_or_ge n 651798561 with hs4 | hs4
          · -- n < 651798561
            rcases Nat.lt_or_ge n 651618705 with hs5 | hs5
            · -- n < 651618705
              exact Brocard.berndt_galway_chunk_3623 n m (by omega) (by omega) h
            · -- n >= 651618705
              exact Brocard.berndt_galway_chunk_3624 n m (by omega) (by omega) h
          · -- n >= 651798561
            exact Brocard.berndt_galway_chunk_3625 n m (by omega) (by omega) h
        · -- n >= 651978417
          rcases Nat.lt_or_ge n 652338129 with hs4 | hs4
          · -- n < 652338129
            rcases Nat.lt_or_ge n 652158273 with hs5 | hs5
            · -- n < 652158273
              exact Brocard.berndt_galway_chunk_3626 n m (by omega) (by omega) h
            · -- n >= 652158273
              exact Brocard.berndt_galway_chunk_3627 n m (by omega) (by omega) h
          · -- n >= 652338129
            exact Brocard.berndt_galway_chunk_3628 n m (by omega) (by omega) h
    · -- n >= 652517985
      rcases Nat.lt_or_ge n 653597122 with hs2 | hs2
      · -- n < 653597122
        rcases Nat.lt_or_ge n 653057553 with hs3 | hs3
        · -- n < 653057553
          rcases Nat.lt_or_ge n 652877697 with hs4 | hs4
          · -- n < 652877697
            rcases Nat.lt_or_ge n 652697841 with hs5 | hs5
            · -- n < 652697841
              exact Brocard.berndt_galway_chunk_3629 n m (by omega) (by omega) h
            · -- n >= 652697841
              exact Brocard.berndt_galway_chunk_3630 n m (by omega) (by omega) h
          · -- n >= 652877697
            exact Brocard.berndt_galway_chunk_3631 n m (by omega) (by omega) h
        · -- n >= 653057553
          rcases Nat.lt_or_ge n 653417266 with hs4 | hs4
          · -- n < 653417266
            rcases Nat.lt_or_ge n 653237410 with hs5 | hs5
            · -- n < 653237410
              exact Brocard.berndt_galway_chunk_3632 n m (by omega) (by omega) h
            · -- n >= 653237410
              exact Brocard.berndt_galway_chunk_3633 n m (by omega) (by omega) h
          · -- n >= 653417266
            exact Brocard.berndt_galway_chunk_3634 n m (by omega) (by omega) h
      · -- n >= 653597122
        rcases Nat.lt_or_ge n 654136690 with hs3 | hs3
        · -- n < 654136690
          rcases Nat.lt_or_ge n 653956834 with hs4 | hs4
          · -- n < 653956834
            rcases Nat.lt_or_ge n 653776978 with hs5 | hs5
            · -- n < 653776978
              exact Brocard.berndt_galway_chunk_3635 n m (by omega) (by omega) h
            · -- n >= 653776978
              exact Brocard.berndt_galway_chunk_3636 n m (by omega) (by omega) h
          · -- n >= 653956834
            exact Brocard.berndt_galway_chunk_3637 n m (by omega) (by omega) h
        · -- n >= 654136690
          rcases Nat.lt_or_ge n 654316546 with hs4 | hs4
          · -- n < 654316546
            exact Brocard.berndt_galway_chunk_3638 n m (by omega) (by omega) h
          · -- n >= 654316546
            exact Brocard.berndt_galway_chunk_3639 n m (by omega) (by omega) h
  · -- n >= 654496402
    rcases Nat.lt_or_ge n 656654676 with hs1 | hs1
    · -- n < 656654676
      rcases Nat.lt_or_ge n 655575539 with hs2 | hs2
      · -- n < 655575539
        rcases Nat.lt_or_ge n 655035971 with hs3 | hs3
        · -- n < 655035971
          rcases Nat.lt_or_ge n 654856115 with hs4 | hs4
          · -- n < 654856115
            rcases Nat.lt_or_ge n 654676258 with hs5 | hs5
            · -- n < 654676258
              exact Brocard.berndt_galway_chunk_3640 n m (by omega) (by omega) h
            · -- n >= 654676258
              exact Brocard.berndt_galway_chunk_3641 n m (by omega) (by omega) h
          · -- n >= 654856115
            exact Brocard.berndt_galway_chunk_3642 n m (by omega) (by omega) h
        · -- n >= 655035971
          rcases Nat.lt_or_ge n 655395683 with hs4 | hs4
          · -- n < 655395683
            rcases Nat.lt_or_ge n 655215827 with hs5 | hs5
            · -- n < 655215827
              exact Brocard.berndt_galway_chunk_3643 n m (by omega) (by omega) h
            · -- n >= 655215827
              exact Brocard.berndt_galway_chunk_3644 n m (by omega) (by omega) h
          · -- n >= 655395683
            exact Brocard.berndt_galway_chunk_3645 n m (by omega) (by omega) h
      · -- n >= 655575539
        rcases Nat.lt_or_ge n 656115107 with hs3 | hs3
        · -- n < 656115107
          rcases Nat.lt_or_ge n 655935251 with hs4 | hs4
          · -- n < 655935251
            rcases Nat.lt_or_ge n 655755395 with hs5 | hs5
            · -- n < 655755395
              exact Brocard.berndt_galway_chunk_3646 n m (by omega) (by omega) h
            · -- n >= 655755395
              exact Brocard.berndt_galway_chunk_3647 n m (by omega) (by omega) h
          · -- n >= 655935251
            exact Brocard.berndt_galway_chunk_3648 n m (by omega) (by omega) h
        · -- n >= 656115107
          rcases Nat.lt_or_ge n 656474820 with hs4 | hs4
          · -- n < 656474820
            rcases Nat.lt_or_ge n 656294964 with hs5 | hs5
            · -- n < 656294964
              exact Brocard.berndt_galway_chunk_3649 n m (by omega) (by omega) h
            · -- n >= 656294964
              exact Brocard.berndt_galway_chunk_3650 n m (by omega) (by omega) h
          · -- n >= 656474820
            exact Brocard.berndt_galway_chunk_3651 n m (by omega) (by omega) h
    · -- n >= 656654676
      rcases Nat.lt_or_ge n 657733812 with hs2 | hs2
      · -- n < 657733812
        rcases Nat.lt_or_ge n 657194244 with hs3 | hs3
        · -- n < 657194244
          rcases Nat.lt_or_ge n 657014388 with hs4 | hs4
          · -- n < 657014388
            rcases Nat.lt_or_ge n 656834532 with hs5 | hs5
            · -- n < 656834532
              exact Brocard.berndt_galway_chunk_3652 n m (by omega) (by omega) h
            · -- n >= 656834532
              exact Brocard.berndt_galway_chunk_3653 n m (by omega) (by omega) h
          · -- n >= 657014388
            exact Brocard.berndt_galway_chunk_3654 n m (by omega) (by omega) h
        · -- n >= 657194244
          rcases Nat.lt_or_ge n 657553956 with hs4 | hs4
          · -- n < 657553956
            rcases Nat.lt_or_ge n 657374100 with hs5 | hs5
            · -- n < 657374100
              exact Brocard.berndt_galway_chunk_3655 n m (by omega) (by omega) h
            · -- n >= 657374100
              exact Brocard.berndt_galway_chunk_3656 n m (by omega) (by omega) h
          · -- n >= 657553956
            exact Brocard.berndt_galway_chunk_3657 n m (by omega) (by omega) h
      · -- n >= 657733812
        rcases Nat.lt_or_ge n 658273381 with hs3 | hs3
        · -- n < 658273381
          rcases Nat.lt_or_ge n 658093525 with hs4 | hs4
          · -- n < 658093525
            rcases Nat.lt_or_ge n 657913669 with hs5 | hs5
            · -- n < 657913669
              exact Brocard.berndt_galway_chunk_3658 n m (by omega) (by omega) h
            · -- n >= 657913669
              exact Brocard.berndt_galway_chunk_3659 n m (by omega) (by omega) h
          · -- n >= 658093525
            exact Brocard.berndt_galway_chunk_3660 n m (by omega) (by omega) h
        · -- n >= 658273381
          rcases Nat.lt_or_ge n 658453237 with hs4 | hs4
          · -- n < 658453237
            exact Brocard.berndt_galway_chunk_3661 n m (by omega) (by omega) h
          · -- n >= 658453237
            exact Brocard.berndt_galway_chunk_3662 n m (by omega) (by omega) h
