-- Prove2me | solution 1 for Brocard.berndt_galway_group_105
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:11:58.369322+00:00
-- url     : https://prove2.me/submissions/6bdb205a-27bc-4994-af42-17dfa4a16df2

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_4821
import Theorems.Thm_Brocard_berndt_galway_chunk_4822
import Theorems.Thm_Brocard_berndt_galway_chunk_4823
import Theorems.Thm_Brocard_berndt_galway_chunk_4824
import Theorems.Thm_Brocard_berndt_galway_chunk_4825
import Theorems.Thm_Brocard_berndt_galway_chunk_4826
import Theorems.Thm_Brocard_berndt_galway_chunk_4827
import Theorems.Thm_Brocard_berndt_galway_chunk_4828
import Theorems.Thm_Brocard_berndt_galway_chunk_4829
import Theorems.Thm_Brocard_berndt_galway_chunk_4830
import Theorems.Thm_Brocard_berndt_galway_chunk_4831
import Theorems.Thm_Brocard_berndt_galway_chunk_4832
import Theorems.Thm_Brocard_berndt_galway_chunk_4833
import Theorems.Thm_Brocard_berndt_galway_chunk_4834
import Theorems.Thm_Brocard_berndt_galway_chunk_4835
import Theorems.Thm_Brocard_berndt_galway_chunk_4836
import Theorems.Thm_Brocard_berndt_galway_chunk_4837
import Theorems.Thm_Brocard_berndt_galway_chunk_4838
import Theorems.Thm_Brocard_berndt_galway_chunk_4839
import Theorems.Thm_Brocard_berndt_galway_chunk_4840
import Theorems.Thm_Brocard_berndt_galway_chunk_4841
import Theorems.Thm_Brocard_berndt_galway_chunk_4842
import Theorems.Thm_Brocard_berndt_galway_chunk_4843
import Theorems.Thm_Brocard_berndt_galway_chunk_4844
import Theorems.Thm_Brocard_berndt_galway_chunk_4845
import Theorems.Thm_Brocard_berndt_galway_chunk_4846
import Theorems.Thm_Brocard_berndt_galway_chunk_4847
import Theorems.Thm_Brocard_berndt_galway_chunk_4848
import Theorems.Thm_Brocard_berndt_galway_chunk_4849
import Theorems.Thm_Brocard_berndt_galway_chunk_4850
import Theorems.Thm_Brocard_berndt_galway_chunk_4851
import Theorems.Thm_Brocard_berndt_galway_chunk_4852
import Theorems.Thm_Brocard_berndt_galway_chunk_4853
import Theorems.Thm_Brocard_berndt_galway_chunk_4854
import Theorems.Thm_Brocard_berndt_galway_chunk_4855
import Theorems.Thm_Brocard_berndt_galway_chunk_4856
import Theorems.Thm_Brocard_berndt_galway_chunk_4857
import Theorems.Thm_Brocard_berndt_galway_chunk_4858
import Theorems.Thm_Brocard_berndt_galway_chunk_4859
import Theorems.Thm_Brocard_berndt_galway_chunk_4860
import Theorems.Thm_Brocard_berndt_galway_chunk_4861
import Theorems.Thm_Brocard_berndt_galway_chunk_4862
import Theorems.Thm_Brocard_berndt_galway_chunk_4863
import Theorems.Thm_Brocard_berndt_galway_chunk_4864
import Theorems.Thm_Brocard_berndt_galway_chunk_4865
import Theorems.Thm_Brocard_berndt_galway_chunk_4866

theorem solution (n m : ℕ) (h1 : 866906474 ≤ n) (h2 : n < 875179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 871043165 with hs0 | hs0
  · -- n < 871043165
    rcases Nat.lt_or_ge n 869064748 with hs1 | hs1
    · -- n < 869064748
      rcases Nat.lt_or_ge n 867985611 with hs2 | hs2
      · -- n < 867985611
        rcases Nat.lt_or_ge n 867446043 with hs3 | hs3
        · -- n < 867446043
          rcases Nat.lt_or_ge n 867266187 with hs4 | hs4
          · -- n < 867266187
            rcases Nat.lt_or_ge n 867086330 with hs5 | hs5
            · -- n < 867086330
              exact Brocard.berndt_galway_chunk_4821 n m (by omega) (by omega) h
            · -- n >= 867086330
              exact Brocard.berndt_galway_chunk_4822 n m (by omega) (by omega) h
          · -- n >= 867266187
            exact Brocard.berndt_galway_chunk_4823 n m (by omega) (by omega) h
        · -- n >= 867446043
          rcases Nat.lt_or_ge n 867805755 with hs4 | hs4
          · -- n < 867805755
            rcases Nat.lt_or_ge n 867625899 with hs5 | hs5
            · -- n < 867625899
              exact Brocard.berndt_galway_chunk_4824 n m (by omega) (by omega) h
            · -- n >= 867625899
              exact Brocard.berndt_galway_chunk_4825 n m (by omega) (by omega) h
          · -- n >= 867805755
            exact Brocard.berndt_galway_chunk_4826 n m (by omega) (by omega) h
      · -- n >= 867985611
        rcases Nat.lt_or_ge n 868525179 with hs3 | hs3
        · -- n < 868525179
          rcases Nat.lt_or_ge n 868345323 with hs4 | hs4
          · -- n < 868345323
            rcases Nat.lt_or_ge n 868165467 with hs5 | hs5
            · -- n < 868165467
              exact Brocard.berndt_galway_chunk_4827 n m (by omega) (by omega) h
            · -- n >= 868165467
              exact Brocard.berndt_galway_chunk_4828 n m (by omega) (by omega) h
          · -- n >= 868345323
            exact Brocard.berndt_galway_chunk_4829 n m (by omega) (by omega) h
        · -- n >= 868525179
          rcases Nat.lt_or_ge n 868884892 with hs4 | hs4
          · -- n < 868884892
            rcases Nat.lt_or_ge n 868705035 with hs5 | hs5
            · -- n < 868705035
              exact Brocard.berndt_galway_chunk_4830 n m (by omega) (by omega) h
            · -- n >= 868705035
              exact Brocard.berndt_galway_chunk_4831 n m (by omega) (by omega) h
          · -- n >= 868884892
            exact Brocard.berndt_galway_chunk_4832 n m (by omega) (by omega) h
    · -- n >= 869064748
      rcases Nat.lt_or_ge n 870143884 with hs2 | hs2
      · -- n < 870143884
        rcases Nat.lt_or_ge n 869604316 with hs3 | hs3
        · -- n < 869604316
          rcases Nat.lt_or_ge n 869424460 with hs4 | hs4
          · -- n < 869424460
            rcases Nat.lt_or_ge n 869244604 with hs5 | hs5
            · -- n < 869244604
              exact Brocard.berndt_galway_chunk_4833 n m (by omega) (by omega) h
            · -- n >= 869244604
              exact Brocard.berndt_galway_chunk_4834 n m (by omega) (by omega) h
          · -- n >= 869424460
            exact Brocard.berndt_galway_chunk_4835 n m (by omega) (by omega) h
        · -- n >= 869604316
          rcases Nat.lt_or_ge n 869964028 with hs4 | hs4
          · -- n < 869964028
            rcases Nat.lt_or_ge n 869784172 with hs5 | hs5
            · -- n < 869784172
              exact Brocard.berndt_galway_chunk_4836 n m (by omega) (by omega) h
            · -- n >= 869784172
              exact Brocard.berndt_galway_chunk_4837 n m (by omega) (by omega) h
          · -- n >= 869964028
            exact Brocard.berndt_galway_chunk_4838 n m (by omega) (by omega) h
      · -- n >= 870143884
        rcases Nat.lt_or_ge n 870683453 with hs3 | hs3
        · -- n < 870683453
          rcases Nat.lt_or_ge n 870503597 with hs4 | hs4
          · -- n < 870503597
            rcases Nat.lt_or_ge n 870323741 with hs5 | hs5
            · -- n < 870323741
              exact Brocard.berndt_galway_chunk_4839 n m (by omega) (by omega) h
            · -- n >= 870323741
              exact Brocard.berndt_galway_chunk_4840 n m (by omega) (by omega) h
          · -- n >= 870503597
            exact Brocard.berndt_galway_chunk_4841 n m (by omega) (by omega) h
        · -- n >= 870683453
          rcases Nat.lt_or_ge n 870863309 with hs4 | hs4
          · -- n < 870863309
            exact Brocard.berndt_galway_chunk_4842 n m (by omega) (by omega) h
          · -- n >= 870863309
            exact Brocard.berndt_galway_chunk_4843 n m (by omega) (by omega) h
  · -- n >= 871043165
    rcases Nat.lt_or_ge n 873201438 with hs1 | hs1
    · -- n < 873201438
      rcases Nat.lt_or_ge n 872122302 with hs2 | hs2
      · -- n < 872122302
        rcases Nat.lt_or_ge n 871582733 with hs3 | hs3
        · -- n < 871582733
          rcases Nat.lt_or_ge n 871402877 with hs4 | hs4
          · -- n < 871402877
            rcases Nat.lt_or_ge n 871223021 with hs5 | hs5
            · -- n < 871223021
              exact Brocard.berndt_galway_chunk_4844 n m (by omega) (by omega) h
            · -- n >= 871223021
              exact Brocard.berndt_galway_chunk_4845 n m (by omega) (by omega) h
          · -- n >= 871402877
            exact Brocard.berndt_galway_chunk_4846 n m (by omega) (by omega) h
        · -- n >= 871582733
          rcases Nat.lt_or_ge n 871942446 with hs4 | hs4
          · -- n < 871942446
            rcases Nat.lt_or_ge n 871762589 with hs5 | hs5
            · -- n < 871762589
              exact Brocard.berndt_galway_chunk_4847 n m (by omega) (by omega) h
            · -- n >= 871762589
              exact Brocard.berndt_galway_chunk_4848 n m (by omega) (by omega) h
          · -- n >= 871942446
            exact Brocard.berndt_galway_chunk_4849 n m (by omega) (by omega) h
      · -- n >= 872122302
        rcases Nat.lt_or_ge n 872661870 with hs3 | hs3
        · -- n < 872661870
          rcases Nat.lt_or_ge n 872482014 with hs4 | hs4
          · -- n < 872482014
            rcases Nat.lt_or_ge n 872302158 with hs5 | hs5
            · -- n < 872302158
              exact Brocard.berndt_galway_chunk_4850 n m (by omega) (by omega) h
            · -- n >= 872302158
              exact Brocard.berndt_galway_chunk_4851 n m (by omega) (by omega) h
          · -- n >= 872482014
            exact Brocard.berndt_galway_chunk_4852 n m (by omega) (by omega) h
        · -- n >= 872661870
          rcases Nat.lt_or_ge n 873021582 with hs4 | hs4
          · -- n < 873021582
            rcases Nat.lt_or_ge n 872841726 with hs5 | hs5
            · -- n < 872841726
              exact Brocard.berndt_galway_chunk_4853 n m (by omega) (by omega) h
            · -- n >= 872841726
              exact Brocard.berndt_galway_chunk_4854 n m (by omega) (by omega) h
          · -- n >= 873021582
            exact Brocard.berndt_galway_chunk_4855 n m (by omega) (by omega) h
    · -- n >= 873201438
      rcases Nat.lt_or_ge n 874280575 with hs2 | hs2
      · -- n < 874280575
        rcases Nat.lt_or_ge n 873741007 with hs3 | hs3
        · -- n < 873741007
          rcases Nat.lt_or_ge n 873561151 with hs4 | hs4
          · -- n < 873561151
            rcases Nat.lt_or_ge n 873381294 with hs5 | hs5
            · -- n < 873381294
              exact Brocard.berndt_galway_chunk_4856 n m (by omega) (by omega) h
            · -- n >= 873381294
              exact Brocard.berndt_galway_chunk_4857 n m (by omega) (by omega) h
          · -- n >= 873561151
            exact Brocard.berndt_galway_chunk_4858 n m (by omega) (by omega) h
        · -- n >= 873741007
          rcases Nat.lt_or_ge n 874100719 with hs4 | hs4
          · -- n < 874100719
            rcases Nat.lt_or_ge n 873920863 with hs5 | hs5
            · -- n < 873920863
              exact Brocard.berndt_galway_chunk_4859 n m (by omega) (by omega) h
            · -- n >= 873920863
              exact Brocard.berndt_galway_chunk_4860 n m (by omega) (by omega) h
          · -- n >= 874100719
            exact Brocard.berndt_galway_chunk_4861 n m (by omega) (by omega) h
      · -- n >= 874280575
        rcases Nat.lt_or_ge n 874820143 with hs3 | hs3
        · -- n < 874820143
          rcases Nat.lt_or_ge n 874640287 with hs4 | hs4
          · -- n < 874640287
            rcases Nat.lt_or_ge n 874460431 with hs5 | hs5
            · -- n < 874460431
              exact Brocard.berndt_galway_chunk_4862 n m (by omega) (by omega) h
            · -- n >= 874460431
              exact Brocard.berndt_galway_chunk_4863 n m (by omega) (by omega) h
          · -- n >= 874640287
            exact Brocard.berndt_galway_chunk_4864 n m (by omega) (by omega) h
        · -- n >= 874820143
          rcases Nat.lt_or_ge n 875000000 with hs4 | hs4
          · -- n < 875000000
            exact Brocard.berndt_galway_chunk_4865 n m (by omega) (by omega) h
          · -- n >= 875000000
            exact Brocard.berndt_galway_chunk_4866 n m (by omega) (by omega) h
