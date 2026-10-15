-- Prove2me | solution 1 for Brocard.berndt_galway_group_083
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:59:03.551656+00:00
-- url     : https://prove2.me/submissions/03b3385b-7604-4dbd-a361-29eb2ad3b6bc

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_3801
import Theorems.Thm_Brocard_berndt_galway_chunk_3802
import Theorems.Thm_Brocard_berndt_galway_chunk_3803
import Theorems.Thm_Brocard_berndt_galway_chunk_3804
import Theorems.Thm_Brocard_berndt_galway_chunk_3805
import Theorems.Thm_Brocard_berndt_galway_chunk_3806
import Theorems.Thm_Brocard_berndt_galway_chunk_3807
import Theorems.Thm_Brocard_berndt_galway_chunk_3808
import Theorems.Thm_Brocard_berndt_galway_chunk_3809
import Theorems.Thm_Brocard_berndt_galway_chunk_3810
import Theorems.Thm_Brocard_berndt_galway_chunk_3811
import Theorems.Thm_Brocard_berndt_galway_chunk_3812
import Theorems.Thm_Brocard_berndt_galway_chunk_3813
import Theorems.Thm_Brocard_berndt_galway_chunk_3814
import Theorems.Thm_Brocard_berndt_galway_chunk_3815
import Theorems.Thm_Brocard_berndt_galway_chunk_3816
import Theorems.Thm_Brocard_berndt_galway_chunk_3817
import Theorems.Thm_Brocard_berndt_galway_chunk_3818
import Theorems.Thm_Brocard_berndt_galway_chunk_3819
import Theorems.Thm_Brocard_berndt_galway_chunk_3820
import Theorems.Thm_Brocard_berndt_galway_chunk_3821
import Theorems.Thm_Brocard_berndt_galway_chunk_3822
import Theorems.Thm_Brocard_berndt_galway_chunk_3823
import Theorems.Thm_Brocard_berndt_galway_chunk_3824
import Theorems.Thm_Brocard_berndt_galway_chunk_3825
import Theorems.Thm_Brocard_berndt_galway_chunk_3826
import Theorems.Thm_Brocard_berndt_galway_chunk_3827
import Theorems.Thm_Brocard_berndt_galway_chunk_3828
import Theorems.Thm_Brocard_berndt_galway_chunk_3829
import Theorems.Thm_Brocard_berndt_galway_chunk_3830
import Theorems.Thm_Brocard_berndt_galway_chunk_3831
import Theorems.Thm_Brocard_berndt_galway_chunk_3832
import Theorems.Thm_Brocard_berndt_galway_chunk_3833
import Theorems.Thm_Brocard_berndt_galway_chunk_3834
import Theorems.Thm_Brocard_berndt_galway_chunk_3835
import Theorems.Thm_Brocard_berndt_galway_chunk_3836
import Theorems.Thm_Brocard_berndt_galway_chunk_3837
import Theorems.Thm_Brocard_berndt_galway_chunk_3838
import Theorems.Thm_Brocard_berndt_galway_chunk_3839
import Theorems.Thm_Brocard_berndt_galway_chunk_3840
import Theorems.Thm_Brocard_berndt_galway_chunk_3841
import Theorems.Thm_Brocard_berndt_galway_chunk_3842
import Theorems.Thm_Brocard_berndt_galway_chunk_3843
import Theorems.Thm_Brocard_berndt_galway_chunk_3844
import Theorems.Thm_Brocard_berndt_galway_chunk_3845
import Theorems.Thm_Brocard_berndt_galway_chunk_3846

theorem solution (n m : ℕ) (h1 : 683453237 ≤ n) (h2 : n < 691726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 687589928 with hs0 | hs0
  · -- n < 687589928
    rcases Nat.lt_or_ge n 685611510 with hs1 | hs1
    · -- n < 685611510
      rcases Nat.lt_or_ge n 684532374 with hs2 | hs2
      · -- n < 684532374
        rcases Nat.lt_or_ge n 683992805 with hs3 | hs3
        · -- n < 683992805
          rcases Nat.lt_or_ge n 683812949 with hs4 | hs4
          · -- n < 683812949
            rcases Nat.lt_or_ge n 683633093 with hs5 | hs5
            · -- n < 683633093
              exact Brocard.berndt_galway_chunk_3801 n m (by omega) (by omega) h
            · -- n >= 683633093
              exact Brocard.berndt_galway_chunk_3802 n m (by omega) (by omega) h
          · -- n >= 683812949
            exact Brocard.berndt_galway_chunk_3803 n m (by omega) (by omega) h
        · -- n >= 683992805
          rcases Nat.lt_or_ge n 684352517 with hs4 | hs4
          · -- n < 684352517
            rcases Nat.lt_or_ge n 684172661 with hs5 | hs5
            · -- n < 684172661
              exact Brocard.berndt_galway_chunk_3804 n m (by omega) (by omega) h
            · -- n >= 684172661
              exact Brocard.berndt_galway_chunk_3805 n m (by omega) (by omega) h
          · -- n >= 684352517
            exact Brocard.berndt_galway_chunk_3806 n m (by omega) (by omega) h
      · -- n >= 684532374
        rcases Nat.lt_or_ge n 685071942 with hs3 | hs3
        · -- n < 685071942
          rcases Nat.lt_or_ge n 684892086 with hs4 | hs4
          · -- n < 684892086
            rcases Nat.lt_or_ge n 684712230 with hs5 | hs5
            · -- n < 684712230
              exact Brocard.berndt_galway_chunk_3807 n m (by omega) (by omega) h
            · -- n >= 684712230
              exact Brocard.berndt_galway_chunk_3808 n m (by omega) (by omega) h
          · -- n >= 684892086
            exact Brocard.berndt_galway_chunk_3809 n m (by omega) (by omega) h
        · -- n >= 685071942
          rcases Nat.lt_or_ge n 685431654 with hs4 | hs4
          · -- n < 685431654
            rcases Nat.lt_or_ge n 685251798 with hs5 | hs5
            · -- n < 685251798
              exact Brocard.berndt_galway_chunk_3810 n m (by omega) (by omega) h
            · -- n >= 685251798
              exact Brocard.berndt_galway_chunk_3811 n m (by omega) (by omega) h
          · -- n >= 685431654
            exact Brocard.berndt_galway_chunk_3812 n m (by omega) (by omega) h
    · -- n >= 685611510
      rcases Nat.lt_or_ge n 686690647 with hs2 | hs2
      · -- n < 686690647
        rcases Nat.lt_or_ge n 686151079 with hs3 | hs3
        · -- n < 686151079
          rcases Nat.lt_or_ge n 685971223 with hs4 | hs4
          · -- n < 685971223
            rcases Nat.lt_or_ge n 685791366 with hs5 | hs5
            · -- n < 685791366
              exact Brocard.berndt_galway_chunk_3813 n m (by omega) (by omega) h
            · -- n >= 685791366
              exact Brocard.berndt_galway_chunk_3814 n m (by omega) (by omega) h
          · -- n >= 685971223
            exact Brocard.berndt_galway_chunk_3815 n m (by omega) (by omega) h
        · -- n >= 686151079
          rcases Nat.lt_or_ge n 686510791 with hs4 | hs4
          · -- n < 686510791
            rcases Nat.lt_or_ge n 686330935 with hs5 | hs5
            · -- n < 686330935
              exact Brocard.berndt_galway_chunk_3816 n m (by omega) (by omega) h
            · -- n >= 686330935
              exact Brocard.berndt_galway_chunk_3817 n m (by omega) (by omega) h
          · -- n >= 686510791
            exact Brocard.berndt_galway_chunk_3818 n m (by omega) (by omega) h
      · -- n >= 686690647
        rcases Nat.lt_or_ge n 687230215 with hs3 | hs3
        · -- n < 687230215
          rcases Nat.lt_or_ge n 687050359 with hs4 | hs4
          · -- n < 687050359
            rcases Nat.lt_or_ge n 686870503 with hs5 | hs5
            · -- n < 686870503
              exact Brocard.berndt_galway_chunk_3819 n m (by omega) (by omega) h
            · -- n >= 686870503
              exact Brocard.berndt_galway_chunk_3820 n m (by omega) (by omega) h
          · -- n >= 687050359
            exact Brocard.berndt_galway_chunk_3821 n m (by omega) (by omega) h
        · -- n >= 687230215
          rcases Nat.lt_or_ge n 687410071 with hs4 | hs4
          · -- n < 687410071
            exact Brocard.berndt_galway_chunk_3822 n m (by omega) (by omega) h
          · -- n >= 687410071
            exact Brocard.berndt_galway_chunk_3823 n m (by omega) (by omega) h
  · -- n >= 687589928
    rcases Nat.lt_or_ge n 689748201 with hs1 | hs1
    · -- n < 689748201
      rcases Nat.lt_or_ge n 688669064 with hs2 | hs2
      · -- n < 688669064
        rcases Nat.lt_or_ge n 688129496 with hs3 | hs3
        · -- n < 688129496
          rcases Nat.lt_or_ge n 687949640 with hs4 | hs4
          · -- n < 687949640
            rcases Nat.lt_or_ge n 687769784 with hs5 | hs5
            · -- n < 687769784
              exact Brocard.berndt_galway_chunk_3824 n m (by omega) (by omega) h
            · -- n >= 687769784
              exact Brocard.berndt_galway_chunk_3825 n m (by omega) (by omega) h
          · -- n >= 687949640
            exact Brocard.berndt_galway_chunk_3826 n m (by omega) (by omega) h
        · -- n >= 688129496
          rcases Nat.lt_or_ge n 688489208 with hs4 | hs4
          · -- n < 688489208
            rcases Nat.lt_or_ge n 688309352 with hs5 | hs5
            · -- n < 688309352
              exact Brocard.berndt_galway_chunk_3827 n m (by omega) (by omega) h
            · -- n >= 688309352
              exact Brocard.berndt_galway_chunk_3828 n m (by omega) (by omega) h
          · -- n >= 688489208
            exact Brocard.berndt_galway_chunk_3829 n m (by omega) (by omega) h
      · -- n >= 688669064
        rcases Nat.lt_or_ge n 689208633 with hs3 | hs3
        · -- n < 689208633
          rcases Nat.lt_or_ge n 689028776 with hs4 | hs4
          · -- n < 689028776
            rcases Nat.lt_or_ge n 688848920 with hs5 | hs5
            · -- n < 688848920
              exact Brocard.berndt_galway_chunk_3830 n m (by omega) (by omega) h
            · -- n >= 688848920
              exact Brocard.berndt_galway_chunk_3831 n m (by omega) (by omega) h
          · -- n >= 689028776
            exact Brocard.berndt_galway_chunk_3832 n m (by omega) (by omega) h
        · -- n >= 689208633
          rcases Nat.lt_or_ge n 689568345 with hs4 | hs4
          · -- n < 689568345
            rcases Nat.lt_or_ge n 689388489 with hs5 | hs5
            · -- n < 689388489
              exact Brocard.berndt_galway_chunk_3833 n m (by omega) (by omega) h
            · -- n >= 689388489
              exact Brocard.berndt_galway_chunk_3834 n m (by omega) (by omega) h
          · -- n >= 689568345
            exact Brocard.berndt_galway_chunk_3835 n m (by omega) (by omega) h
    · -- n >= 689748201
      rcases Nat.lt_or_ge n 690827338 with hs2 | hs2
      · -- n < 690827338
        rcases Nat.lt_or_ge n 690287769 with hs3 | hs3
        · -- n < 690287769
          rcases Nat.lt_or_ge n 690107913 with hs4 | hs4
          · -- n < 690107913
            rcases Nat.lt_or_ge n 689928057 with hs5 | hs5
            · -- n < 689928057
              exact Brocard.berndt_galway_chunk_3836 n m (by omega) (by omega) h
            · -- n >= 689928057
              exact Brocard.berndt_galway_chunk_3837 n m (by omega) (by omega) h
          · -- n >= 690107913
            exact Brocard.berndt_galway_chunk_3838 n m (by omega) (by omega) h
        · -- n >= 690287769
          rcases Nat.lt_or_ge n 690647482 with hs4 | hs4
          · -- n < 690647482
            rcases Nat.lt_or_ge n 690467625 with hs5 | hs5
            · -- n < 690467625
              exact Brocard.berndt_galway_chunk_3839 n m (by omega) (by omega) h
            · -- n >= 690467625
              exact Brocard.berndt_galway_chunk_3840 n m (by omega) (by omega) h
          · -- n >= 690647482
            exact Brocard.berndt_galway_chunk_3841 n m (by omega) (by omega) h
      · -- n >= 690827338
        rcases Nat.lt_or_ge n 691366906 with hs3 | hs3
        · -- n < 691366906
          rcases Nat.lt_or_ge n 691187050 with hs4 | hs4
          · -- n < 691187050
            rcases Nat.lt_or_ge n 691007194 with hs5 | hs5
            · -- n < 691007194
              exact Brocard.berndt_galway_chunk_3842 n m (by omega) (by omega) h
            · -- n >= 691007194
              exact Brocard.berndt_galway_chunk_3843 n m (by omega) (by omega) h
          · -- n >= 691187050
            exact Brocard.berndt_galway_chunk_3844 n m (by omega) (by omega) h
        · -- n >= 691366906
          rcases Nat.lt_or_ge n 691546762 with hs4 | hs4
          · -- n < 691546762
            exact Brocard.berndt_galway_chunk_3845 n m (by omega) (by omega) h
          · -- n >= 691546762
            exact Brocard.berndt_galway_chunk_3846 n m (by omega) (by omega) h
