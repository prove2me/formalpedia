-- Prove2me | solution 1 for Brocard.berndt_galway_group_103
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:52:07.395454+00:00
-- url     : https://prove2.me/submissions/8a2bb527-8bb0-4f84-9261-df814ec449c5

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_4729
import Theorems.Thm_Brocard_berndt_galway_chunk_4730
import Theorems.Thm_Brocard_berndt_galway_chunk_4731
import Theorems.Thm_Brocard_berndt_galway_chunk_4732
import Theorems.Thm_Brocard_berndt_galway_chunk_4733
import Theorems.Thm_Brocard_berndt_galway_chunk_4734
import Theorems.Thm_Brocard_berndt_galway_chunk_4735
import Theorems.Thm_Brocard_berndt_galway_chunk_4736
import Theorems.Thm_Brocard_berndt_galway_chunk_4737
import Theorems.Thm_Brocard_berndt_galway_chunk_4738
import Theorems.Thm_Brocard_berndt_galway_chunk_4739
import Theorems.Thm_Brocard_berndt_galway_chunk_4740
import Theorems.Thm_Brocard_berndt_galway_chunk_4741
import Theorems.Thm_Brocard_berndt_galway_chunk_4742
import Theorems.Thm_Brocard_berndt_galway_chunk_4743
import Theorems.Thm_Brocard_berndt_galway_chunk_4744
import Theorems.Thm_Brocard_berndt_galway_chunk_4745
import Theorems.Thm_Brocard_berndt_galway_chunk_4746
import Theorems.Thm_Brocard_berndt_galway_chunk_4747
import Theorems.Thm_Brocard_berndt_galway_chunk_4748
import Theorems.Thm_Brocard_berndt_galway_chunk_4749
import Theorems.Thm_Brocard_berndt_galway_chunk_4750
import Theorems.Thm_Brocard_berndt_galway_chunk_4751
import Theorems.Thm_Brocard_berndt_galway_chunk_4752
import Theorems.Thm_Brocard_berndt_galway_chunk_4753
import Theorems.Thm_Brocard_berndt_galway_chunk_4754
import Theorems.Thm_Brocard_berndt_galway_chunk_4755
import Theorems.Thm_Brocard_berndt_galway_chunk_4756
import Theorems.Thm_Brocard_berndt_galway_chunk_4757
import Theorems.Thm_Brocard_berndt_galway_chunk_4758
import Theorems.Thm_Brocard_berndt_galway_chunk_4759
import Theorems.Thm_Brocard_berndt_galway_chunk_4760
import Theorems.Thm_Brocard_berndt_galway_chunk_4761
import Theorems.Thm_Brocard_berndt_galway_chunk_4762
import Theorems.Thm_Brocard_berndt_galway_chunk_4763
import Theorems.Thm_Brocard_berndt_galway_chunk_4764
import Theorems.Thm_Brocard_berndt_galway_chunk_4765
import Theorems.Thm_Brocard_berndt_galway_chunk_4766
import Theorems.Thm_Brocard_berndt_galway_chunk_4767
import Theorems.Thm_Brocard_berndt_galway_chunk_4768
import Theorems.Thm_Brocard_berndt_galway_chunk_4769
import Theorems.Thm_Brocard_berndt_galway_chunk_4770
import Theorems.Thm_Brocard_berndt_galway_chunk_4771
import Theorems.Thm_Brocard_berndt_galway_chunk_4772
import Theorems.Thm_Brocard_berndt_galway_chunk_4773
import Theorems.Thm_Brocard_berndt_galway_chunk_4774

theorem solution (n m : ℕ) (h1 : 850359712 ≤ n) (h2 : n < 858633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 854496402 with hs0 | hs0
  · -- n < 854496402
    rcases Nat.lt_or_ge n 852517985 with hs1 | hs1
    · -- n < 852517985
      rcases Nat.lt_or_ge n 851438848 with hs2 | hs2
      · -- n < 851438848
        rcases Nat.lt_or_ge n 850899280 with hs3 | hs3
        · -- n < 850899280
          rcases Nat.lt_or_ge n 850719424 with hs4 | hs4
          · -- n < 850719424
            rcases Nat.lt_or_ge n 850539568 with hs5 | hs5
            · -- n < 850539568
              exact Brocard.berndt_galway_chunk_4729 n m (by omega) (by omega) h
            · -- n >= 850539568
              exact Brocard.berndt_galway_chunk_4730 n m (by omega) (by omega) h
          · -- n >= 850719424
            exact Brocard.berndt_galway_chunk_4731 n m (by omega) (by omega) h
        · -- n >= 850899280
          rcases Nat.lt_or_ge n 851258992 with hs4 | hs4
          · -- n < 851258992
            rcases Nat.lt_or_ge n 851079136 with hs5 | hs5
            · -- n < 851079136
              exact Brocard.berndt_galway_chunk_4732 n m (by omega) (by omega) h
            · -- n >= 851079136
              exact Brocard.berndt_galway_chunk_4733 n m (by omega) (by omega) h
          · -- n >= 851258992
            exact Brocard.berndt_galway_chunk_4734 n m (by omega) (by omega) h
      · -- n >= 851438848
        rcases Nat.lt_or_ge n 851978417 with hs3 | hs3
        · -- n < 851978417
          rcases Nat.lt_or_ge n 851798561 with hs4 | hs4
          · -- n < 851798561
            rcases Nat.lt_or_ge n 851618705 with hs5 | hs5
            · -- n < 851618705
              exact Brocard.berndt_galway_chunk_4735 n m (by omega) (by omega) h
            · -- n >= 851618705
              exact Brocard.berndt_galway_chunk_4736 n m (by omega) (by omega) h
          · -- n >= 851798561
            exact Brocard.berndt_galway_chunk_4737 n m (by omega) (by omega) h
        · -- n >= 851978417
          rcases Nat.lt_or_ge n 852338129 with hs4 | hs4
          · -- n < 852338129
            rcases Nat.lt_or_ge n 852158273 with hs5 | hs5
            · -- n < 852158273
              exact Brocard.berndt_galway_chunk_4738 n m (by omega) (by omega) h
            · -- n >= 852158273
              exact Brocard.berndt_galway_chunk_4739 n m (by omega) (by omega) h
          · -- n >= 852338129
            exact Brocard.berndt_galway_chunk_4740 n m (by omega) (by omega) h
    · -- n >= 852517985
      rcases Nat.lt_or_ge n 853597122 with hs2 | hs2
      · -- n < 853597122
        rcases Nat.lt_or_ge n 853057553 with hs3 | hs3
        · -- n < 853057553
          rcases Nat.lt_or_ge n 852877697 with hs4 | hs4
          · -- n < 852877697
            rcases Nat.lt_or_ge n 852697841 with hs5 | hs5
            · -- n < 852697841
              exact Brocard.berndt_galway_chunk_4741 n m (by omega) (by omega) h
            · -- n >= 852697841
              exact Brocard.berndt_galway_chunk_4742 n m (by omega) (by omega) h
          · -- n >= 852877697
            exact Brocard.berndt_galway_chunk_4743 n m (by omega) (by omega) h
        · -- n >= 853057553
          rcases Nat.lt_or_ge n 853417266 with hs4 | hs4
          · -- n < 853417266
            rcases Nat.lt_or_ge n 853237410 with hs5 | hs5
            · -- n < 853237410
              exact Brocard.berndt_galway_chunk_4744 n m (by omega) (by omega) h
            · -- n >= 853237410
              exact Brocard.berndt_galway_chunk_4745 n m (by omega) (by omega) h
          · -- n >= 853417266
            exact Brocard.berndt_galway_chunk_4746 n m (by omega) (by omega) h
      · -- n >= 853597122
        rcases Nat.lt_or_ge n 854136690 with hs3 | hs3
        · -- n < 854136690
          rcases Nat.lt_or_ge n 853956834 with hs4 | hs4
          · -- n < 853956834
            rcases Nat.lt_or_ge n 853776978 with hs5 | hs5
            · -- n < 853776978
              exact Brocard.berndt_galway_chunk_4747 n m (by omega) (by omega) h
            · -- n >= 853776978
              exact Brocard.berndt_galway_chunk_4748 n m (by omega) (by omega) h
          · -- n >= 853956834
            exact Brocard.berndt_galway_chunk_4749 n m (by omega) (by omega) h
        · -- n >= 854136690
          rcases Nat.lt_or_ge n 854316546 with hs4 | hs4
          · -- n < 854316546
            exact Brocard.berndt_galway_chunk_4750 n m (by omega) (by omega) h
          · -- n >= 854316546
            exact Brocard.berndt_galway_chunk_4751 n m (by omega) (by omega) h
  · -- n >= 854496402
    rcases Nat.lt_or_ge n 856654676 with hs1 | hs1
    · -- n < 856654676
      rcases Nat.lt_or_ge n 855575539 with hs2 | hs2
      · -- n < 855575539
        rcases Nat.lt_or_ge n 855035971 with hs3 | hs3
        · -- n < 855035971
          rcases Nat.lt_or_ge n 854856115 with hs4 | hs4
          · -- n < 854856115
            rcases Nat.lt_or_ge n 854676258 with hs5 | hs5
            · -- n < 854676258
              exact Brocard.berndt_galway_chunk_4752 n m (by omega) (by omega) h
            · -- n >= 854676258
              exact Brocard.berndt_galway_chunk_4753 n m (by omega) (by omega) h
          · -- n >= 854856115
            exact Brocard.berndt_galway_chunk_4754 n m (by omega) (by omega) h
        · -- n >= 855035971
          rcases Nat.lt_or_ge n 855395683 with hs4 | hs4
          · -- n < 855395683
            rcases Nat.lt_or_ge n 855215827 with hs5 | hs5
            · -- n < 855215827
              exact Brocard.berndt_galway_chunk_4755 n m (by omega) (by omega) h
            · -- n >= 855215827
              exact Brocard.berndt_galway_chunk_4756 n m (by omega) (by omega) h
          · -- n >= 855395683
            exact Brocard.berndt_galway_chunk_4757 n m (by omega) (by omega) h
      · -- n >= 855575539
        rcases Nat.lt_or_ge n 856115107 with hs3 | hs3
        · -- n < 856115107
          rcases Nat.lt_or_ge n 855935251 with hs4 | hs4
          · -- n < 855935251
            rcases Nat.lt_or_ge n 855755395 with hs5 | hs5
            · -- n < 855755395
              exact Brocard.berndt_galway_chunk_4758 n m (by omega) (by omega) h
            · -- n >= 855755395
              exact Brocard.berndt_galway_chunk_4759 n m (by omega) (by omega) h
          · -- n >= 855935251
            exact Brocard.berndt_galway_chunk_4760 n m (by omega) (by omega) h
        · -- n >= 856115107
          rcases Nat.lt_or_ge n 856474820 with hs4 | hs4
          · -- n < 856474820
            rcases Nat.lt_or_ge n 856294964 with hs5 | hs5
            · -- n < 856294964
              exact Brocard.berndt_galway_chunk_4761 n m (by omega) (by omega) h
            · -- n >= 856294964
              exact Brocard.berndt_galway_chunk_4762 n m (by omega) (by omega) h
          · -- n >= 856474820
            exact Brocard.berndt_galway_chunk_4763 n m (by omega) (by omega) h
    · -- n >= 856654676
      rcases Nat.lt_or_ge n 857733812 with hs2 | hs2
      · -- n < 857733812
        rcases Nat.lt_or_ge n 857194244 with hs3 | hs3
        · -- n < 857194244
          rcases Nat.lt_or_ge n 857014388 with hs4 | hs4
          · -- n < 857014388
            rcases Nat.lt_or_ge n 856834532 with hs5 | hs5
            · -- n < 856834532
              exact Brocard.berndt_galway_chunk_4764 n m (by omega) (by omega) h
            · -- n >= 856834532
              exact Brocard.berndt_galway_chunk_4765 n m (by omega) (by omega) h
          · -- n >= 857014388
            exact Brocard.berndt_galway_chunk_4766 n m (by omega) (by omega) h
        · -- n >= 857194244
          rcases Nat.lt_or_ge n 857553956 with hs4 | hs4
          · -- n < 857553956
            rcases Nat.lt_or_ge n 857374100 with hs5 | hs5
            · -- n < 857374100
              exact Brocard.berndt_galway_chunk_4767 n m (by omega) (by omega) h
            · -- n >= 857374100
              exact Brocard.berndt_galway_chunk_4768 n m (by omega) (by omega) h
          · -- n >= 857553956
            exact Brocard.berndt_galway_chunk_4769 n m (by omega) (by omega) h
      · -- n >= 857733812
        rcases Nat.lt_or_ge n 858273381 with hs3 | hs3
        · -- n < 858273381
          rcases Nat.lt_or_ge n 858093525 with hs4 | hs4
          · -- n < 858093525
            rcases Nat.lt_or_ge n 857913669 with hs5 | hs5
            · -- n < 857913669
              exact Brocard.berndt_galway_chunk_4770 n m (by omega) (by omega) h
            · -- n >= 857913669
              exact Brocard.berndt_galway_chunk_4771 n m (by omega) (by omega) h
          · -- n >= 858093525
            exact Brocard.berndt_galway_chunk_4772 n m (by omega) (by omega) h
        · -- n >= 858273381
          rcases Nat.lt_or_ge n 858453237 with hs4 | hs4
          · -- n < 858453237
            exact Brocard.berndt_galway_chunk_4773 n m (by omega) (by omega) h
          · -- n >= 858453237
            exact Brocard.berndt_galway_chunk_4774 n m (by omega) (by omega) h
