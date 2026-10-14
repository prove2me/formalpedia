-- Prove2me | solution 1 for Brocard.berndt_galway_group_017
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:58:37.511162+00:00
-- url     : https://prove2.me/submissions/233e29ee-d21a-447c-9123-f35137f50908

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_0745
import Theorems.Thm_Brocard_berndt_galway_chunk_0746
import Theorems.Thm_Brocard_berndt_galway_chunk_0747
import Theorems.Thm_Brocard_berndt_galway_chunk_0748
import Theorems.Thm_Brocard_berndt_galway_chunk_0749
import Theorems.Thm_Brocard_berndt_galway_chunk_0750
import Theorems.Thm_Brocard_berndt_galway_chunk_0751
import Theorems.Thm_Brocard_berndt_galway_chunk_0752
import Theorems.Thm_Brocard_berndt_galway_chunk_0753
import Theorems.Thm_Brocard_berndt_galway_chunk_0754
import Theorems.Thm_Brocard_berndt_galway_chunk_0755
import Theorems.Thm_Brocard_berndt_galway_chunk_0756
import Theorems.Thm_Brocard_berndt_galway_chunk_0757
import Theorems.Thm_Brocard_berndt_galway_chunk_0758
import Theorems.Thm_Brocard_berndt_galway_chunk_0759
import Theorems.Thm_Brocard_berndt_galway_chunk_0760
import Theorems.Thm_Brocard_berndt_galway_chunk_0761
import Theorems.Thm_Brocard_berndt_galway_chunk_0762
import Theorems.Thm_Brocard_berndt_galway_chunk_0763
import Theorems.Thm_Brocard_berndt_galway_chunk_0764
import Theorems.Thm_Brocard_berndt_galway_chunk_0765
import Theorems.Thm_Brocard_berndt_galway_chunk_0766
import Theorems.Thm_Brocard_berndt_galway_chunk_0767
import Theorems.Thm_Brocard_berndt_galway_chunk_0768
import Theorems.Thm_Brocard_berndt_galway_chunk_0769
import Theorems.Thm_Brocard_berndt_galway_chunk_0770
import Theorems.Thm_Brocard_berndt_galway_chunk_0771
import Theorems.Thm_Brocard_berndt_galway_chunk_0772
import Theorems.Thm_Brocard_berndt_galway_chunk_0773
import Theorems.Thm_Brocard_berndt_galway_chunk_0774
import Theorems.Thm_Brocard_berndt_galway_chunk_0775
import Theorems.Thm_Brocard_berndt_galway_chunk_0776
import Theorems.Thm_Brocard_berndt_galway_chunk_0777
import Theorems.Thm_Brocard_berndt_galway_chunk_0778
import Theorems.Thm_Brocard_berndt_galway_chunk_0779
import Theorems.Thm_Brocard_berndt_galway_chunk_0780
import Theorems.Thm_Brocard_berndt_galway_chunk_0781
import Theorems.Thm_Brocard_berndt_galway_chunk_0782
import Theorems.Thm_Brocard_berndt_galway_chunk_0783
import Theorems.Thm_Brocard_berndt_galway_chunk_0784
import Theorems.Thm_Brocard_berndt_galway_chunk_0785
import Theorems.Thm_Brocard_berndt_galway_chunk_0786
import Theorems.Thm_Brocard_berndt_galway_chunk_0787
import Theorems.Thm_Brocard_berndt_galway_chunk_0788
import Theorems.Thm_Brocard_berndt_galway_chunk_0789
import Theorems.Thm_Brocard_berndt_galway_chunk_0790

theorem solution (n m : ℕ) (h1 : 133812949 ≤ n) (h2 : n < 142086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 137949640 with hs0 | hs0
  · -- n < 137949640
    rcases Nat.lt_or_ge n 135971223 with hs1 | hs1
    · -- n < 135971223
      rcases Nat.lt_or_ge n 134892086 with hs2 | hs2
      · -- n < 134892086
        rcases Nat.lt_or_ge n 134352517 with hs3 | hs3
        · -- n < 134352517
          rcases Nat.lt_or_ge n 134172661 with hs4 | hs4
          · -- n < 134172661
            rcases Nat.lt_or_ge n 133992805 with hs5 | hs5
            · -- n < 133992805
              exact Brocard.berndt_galway_chunk_0745 n m (by omega) (by omega) h
            · -- n >= 133992805
              exact Brocard.berndt_galway_chunk_0746 n m (by omega) (by omega) h
          · -- n >= 134172661
            exact Brocard.berndt_galway_chunk_0747 n m (by omega) (by omega) h
        · -- n >= 134352517
          rcases Nat.lt_or_ge n 134712230 with hs4 | hs4
          · -- n < 134712230
            rcases Nat.lt_or_ge n 134532374 with hs5 | hs5
            · -- n < 134532374
              exact Brocard.berndt_galway_chunk_0748 n m (by omega) (by omega) h
            · -- n >= 134532374
              exact Brocard.berndt_galway_chunk_0749 n m (by omega) (by omega) h
          · -- n >= 134712230
            exact Brocard.berndt_galway_chunk_0750 n m (by omega) (by omega) h
      · -- n >= 134892086
        rcases Nat.lt_or_ge n 135431654 with hs3 | hs3
        · -- n < 135431654
          rcases Nat.lt_or_ge n 135251798 with hs4 | hs4
          · -- n < 135251798
            rcases Nat.lt_or_ge n 135071942 with hs5 | hs5
            · -- n < 135071942
              exact Brocard.berndt_galway_chunk_0751 n m (by omega) (by omega) h
            · -- n >= 135071942
              exact Brocard.berndt_galway_chunk_0752 n m (by omega) (by omega) h
          · -- n >= 135251798
            exact Brocard.berndt_galway_chunk_0753 n m (by omega) (by omega) h
        · -- n >= 135431654
          rcases Nat.lt_or_ge n 135791366 with hs4 | hs4
          · -- n < 135791366
            rcases Nat.lt_or_ge n 135611510 with hs5 | hs5
            · -- n < 135611510
              exact Brocard.berndt_galway_chunk_0754 n m (by omega) (by omega) h
            · -- n >= 135611510
              exact Brocard.berndt_galway_chunk_0755 n m (by omega) (by omega) h
          · -- n >= 135791366
            exact Brocard.berndt_galway_chunk_0756 n m (by omega) (by omega) h
    · -- n >= 135971223
      rcases Nat.lt_or_ge n 137050359 with hs2 | hs2
      · -- n < 137050359
        rcases Nat.lt_or_ge n 136510791 with hs3 | hs3
        · -- n < 136510791
          rcases Nat.lt_or_ge n 136330935 with hs4 | hs4
          · -- n < 136330935
            rcases Nat.lt_or_ge n 136151079 with hs5 | hs5
            · -- n < 136151079
              exact Brocard.berndt_galway_chunk_0757 n m (by omega) (by omega) h
            · -- n >= 136151079
              exact Brocard.berndt_galway_chunk_0758 n m (by omega) (by omega) h
          · -- n >= 136330935
            exact Brocard.berndt_galway_chunk_0759 n m (by omega) (by omega) h
        · -- n >= 136510791
          rcases Nat.lt_or_ge n 136870503 with hs4 | hs4
          · -- n < 136870503
            rcases Nat.lt_or_ge n 136690647 with hs5 | hs5
            · -- n < 136690647
              exact Brocard.berndt_galway_chunk_0760 n m (by omega) (by omega) h
            · -- n >= 136690647
              exact Brocard.berndt_galway_chunk_0761 n m (by omega) (by omega) h
          · -- n >= 136870503
            exact Brocard.berndt_galway_chunk_0762 n m (by omega) (by omega) h
      · -- n >= 137050359
        rcases Nat.lt_or_ge n 137589928 with hs3 | hs3
        · -- n < 137589928
          rcases Nat.lt_or_ge n 137410071 with hs4 | hs4
          · -- n < 137410071
            rcases Nat.lt_or_ge n 137230215 with hs5 | hs5
            · -- n < 137230215
              exact Brocard.berndt_galway_chunk_0763 n m (by omega) (by omega) h
            · -- n >= 137230215
              exact Brocard.berndt_galway_chunk_0764 n m (by omega) (by omega) h
          · -- n >= 137410071
            exact Brocard.berndt_galway_chunk_0765 n m (by omega) (by omega) h
        · -- n >= 137589928
          rcases Nat.lt_or_ge n 137769784 with hs4 | hs4
          · -- n < 137769784
            exact Brocard.berndt_galway_chunk_0766 n m (by omega) (by omega) h
          · -- n >= 137769784
            exact Brocard.berndt_galway_chunk_0767 n m (by omega) (by omega) h
  · -- n >= 137949640
    rcases Nat.lt_or_ge n 140107913 with hs1 | hs1
    · -- n < 140107913
      rcases Nat.lt_or_ge n 139028776 with hs2 | hs2
      · -- n < 139028776
        rcases Nat.lt_or_ge n 138489208 with hs3 | hs3
        · -- n < 138489208
          rcases Nat.lt_or_ge n 138309352 with hs4 | hs4
          · -- n < 138309352
            rcases Nat.lt_or_ge n 138129496 with hs5 | hs5
            · -- n < 138129496
              exact Brocard.berndt_galway_chunk_0768 n m (by omega) (by omega) h
            · -- n >= 138129496
              exact Brocard.berndt_galway_chunk_0769 n m (by omega) (by omega) h
          · -- n >= 138309352
            exact Brocard.berndt_galway_chunk_0770 n m (by omega) (by omega) h
        · -- n >= 138489208
          rcases Nat.lt_or_ge n 138848920 with hs4 | hs4
          · -- n < 138848920
            rcases Nat.lt_or_ge n 138669064 with hs5 | hs5
            · -- n < 138669064
              exact Brocard.berndt_galway_chunk_0771 n m (by omega) (by omega) h
            · -- n >= 138669064
              exact Brocard.berndt_galway_chunk_0772 n m (by omega) (by omega) h
          · -- n >= 138848920
            exact Brocard.berndt_galway_chunk_0773 n m (by omega) (by omega) h
      · -- n >= 139028776
        rcases Nat.lt_or_ge n 139568345 with hs3 | hs3
        · -- n < 139568345
          rcases Nat.lt_or_ge n 139388489 with hs4 | hs4
          · -- n < 139388489
            rcases Nat.lt_or_ge n 139208633 with hs5 | hs5
            · -- n < 139208633
              exact Brocard.berndt_galway_chunk_0774 n m (by omega) (by omega) h
            · -- n >= 139208633
              exact Brocard.berndt_galway_chunk_0775 n m (by omega) (by omega) h
          · -- n >= 139388489
            exact Brocard.berndt_galway_chunk_0776 n m (by omega) (by omega) h
        · -- n >= 139568345
          rcases Nat.lt_or_ge n 139928057 with hs4 | hs4
          · -- n < 139928057
            rcases Nat.lt_or_ge n 139748201 with hs5 | hs5
            · -- n < 139748201
              exact Brocard.berndt_galway_chunk_0777 n m (by omega) (by omega) h
            · -- n >= 139748201
              exact Brocard.berndt_galway_chunk_0778 n m (by omega) (by omega) h
          · -- n >= 139928057
            exact Brocard.berndt_galway_chunk_0779 n m (by omega) (by omega) h
    · -- n >= 140107913
      rcases Nat.lt_or_ge n 141187050 with hs2 | hs2
      · -- n < 141187050
        rcases Nat.lt_or_ge n 140647482 with hs3 | hs3
        · -- n < 140647482
          rcases Nat.lt_or_ge n 140467625 with hs4 | hs4
          · -- n < 140467625
            rcases Nat.lt_or_ge n 140287769 with hs5 | hs5
            · -- n < 140287769
              exact Brocard.berndt_galway_chunk_0780 n m (by omega) (by omega) h
            · -- n >= 140287769
              exact Brocard.berndt_galway_chunk_0781 n m (by omega) (by omega) h
          · -- n >= 140467625
            exact Brocard.berndt_galway_chunk_0782 n m (by omega) (by omega) h
        · -- n >= 140647482
          rcases Nat.lt_or_ge n 141007194 with hs4 | hs4
          · -- n < 141007194
            rcases Nat.lt_or_ge n 140827338 with hs5 | hs5
            · -- n < 140827338
              exact Brocard.berndt_galway_chunk_0783 n m (by omega) (by omega) h
            · -- n >= 140827338
              exact Brocard.berndt_galway_chunk_0784 n m (by omega) (by omega) h
          · -- n >= 141007194
            exact Brocard.berndt_galway_chunk_0785 n m (by omega) (by omega) h
      · -- n >= 141187050
        rcases Nat.lt_or_ge n 141726618 with hs3 | hs3
        · -- n < 141726618
          rcases Nat.lt_or_ge n 141546762 with hs4 | hs4
          · -- n < 141546762
            rcases Nat.lt_or_ge n 141366906 with hs5 | hs5
            · -- n < 141366906
              exact Brocard.berndt_galway_chunk_0786 n m (by omega) (by omega) h
            · -- n >= 141366906
              exact Brocard.berndt_galway_chunk_0787 n m (by omega) (by omega) h
          · -- n >= 141546762
            exact Brocard.berndt_galway_chunk_0788 n m (by omega) (by omega) h
        · -- n >= 141726618
          rcases Nat.lt_or_ge n 141906474 with hs4 | hs4
          · -- n < 141906474
            exact Brocard.berndt_galway_chunk_0789 n m (by omega) (by omega) h
          · -- n >= 141906474
            exact Brocard.berndt_galway_chunk_0790 n m (by omega) (by omega) h
