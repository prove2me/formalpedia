-- Prove2me | solution 1 for Brocard.berndt_galway_group_018
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:15:00.008106+00:00
-- url     : https://prove2.me/submissions/cd2c3bf5-d747-41a0-a858-fd672e8a34c0

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_0791
import Theorems.Thm_Brocard_berndt_galway_chunk_0792
import Theorems.Thm_Brocard_berndt_galway_chunk_0793
import Theorems.Thm_Brocard_berndt_galway_chunk_0794
import Theorems.Thm_Brocard_berndt_galway_chunk_0795
import Theorems.Thm_Brocard_berndt_galway_chunk_0796
import Theorems.Thm_Brocard_berndt_galway_chunk_0797
import Theorems.Thm_Brocard_berndt_galway_chunk_0798
import Theorems.Thm_Brocard_berndt_galway_chunk_0799
import Theorems.Thm_Brocard_berndt_galway_chunk_0800
import Theorems.Thm_Brocard_berndt_galway_chunk_0801
import Theorems.Thm_Brocard_berndt_galway_chunk_0802
import Theorems.Thm_Brocard_berndt_galway_chunk_0803
import Theorems.Thm_Brocard_berndt_galway_chunk_0804
import Theorems.Thm_Brocard_berndt_galway_chunk_0805
import Theorems.Thm_Brocard_berndt_galway_chunk_0806
import Theorems.Thm_Brocard_berndt_galway_chunk_0807
import Theorems.Thm_Brocard_berndt_galway_chunk_0808
import Theorems.Thm_Brocard_berndt_galway_chunk_0809
import Theorems.Thm_Brocard_berndt_galway_chunk_0810
import Theorems.Thm_Brocard_berndt_galway_chunk_0811
import Theorems.Thm_Brocard_berndt_galway_chunk_0812
import Theorems.Thm_Brocard_berndt_galway_chunk_0813
import Theorems.Thm_Brocard_berndt_galway_chunk_0814
import Theorems.Thm_Brocard_berndt_galway_chunk_0815
import Theorems.Thm_Brocard_berndt_galway_chunk_0816
import Theorems.Thm_Brocard_berndt_galway_chunk_0817
import Theorems.Thm_Brocard_berndt_galway_chunk_0818
import Theorems.Thm_Brocard_berndt_galway_chunk_0819
import Theorems.Thm_Brocard_berndt_galway_chunk_0820
import Theorems.Thm_Brocard_berndt_galway_chunk_0821
import Theorems.Thm_Brocard_berndt_galway_chunk_0822
import Theorems.Thm_Brocard_berndt_galway_chunk_0823
import Theorems.Thm_Brocard_berndt_galway_chunk_0824
import Theorems.Thm_Brocard_berndt_galway_chunk_0825
import Theorems.Thm_Brocard_berndt_galway_chunk_0826
import Theorems.Thm_Brocard_berndt_galway_chunk_0827
import Theorems.Thm_Brocard_berndt_galway_chunk_0828
import Theorems.Thm_Brocard_berndt_galway_chunk_0829
import Theorems.Thm_Brocard_berndt_galway_chunk_0830
import Theorems.Thm_Brocard_berndt_galway_chunk_0831
import Theorems.Thm_Brocard_berndt_galway_chunk_0832
import Theorems.Thm_Brocard_berndt_galway_chunk_0833
import Theorems.Thm_Brocard_berndt_galway_chunk_0834
import Theorems.Thm_Brocard_berndt_galway_chunk_0835
import Theorems.Thm_Brocard_berndt_galway_chunk_0836

theorem solution (n m : ℕ) (h1 : 142086330 ≤ n) (h2 : n < 150359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 146223021 with hs0 | hs0
  · -- n < 146223021
    rcases Nat.lt_or_ge n 144244604 with hs1 | hs1
    · -- n < 144244604
      rcases Nat.lt_or_ge n 143165467 with hs2 | hs2
      · -- n < 143165467
        rcases Nat.lt_or_ge n 142625899 with hs3 | hs3
        · -- n < 142625899
          rcases Nat.lt_or_ge n 142446043 with hs4 | hs4
          · -- n < 142446043
            rcases Nat.lt_or_ge n 142266187 with hs5 | hs5
            · -- n < 142266187
              exact Brocard.berndt_galway_chunk_0791 n m (by omega) (by omega) h
            · -- n >= 142266187
              exact Brocard.berndt_galway_chunk_0792 n m (by omega) (by omega) h
          · -- n >= 142446043
            exact Brocard.berndt_galway_chunk_0793 n m (by omega) (by omega) h
        · -- n >= 142625899
          rcases Nat.lt_or_ge n 142985611 with hs4 | hs4
          · -- n < 142985611
            rcases Nat.lt_or_ge n 142805755 with hs5 | hs5
            · -- n < 142805755
              exact Brocard.berndt_galway_chunk_0794 n m (by omega) (by omega) h
            · -- n >= 142805755
              exact Brocard.berndt_galway_chunk_0795 n m (by omega) (by omega) h
          · -- n >= 142985611
            exact Brocard.berndt_galway_chunk_0796 n m (by omega) (by omega) h
      · -- n >= 143165467
        rcases Nat.lt_or_ge n 143705035 with hs3 | hs3
        · -- n < 143705035
          rcases Nat.lt_or_ge n 143525179 with hs4 | hs4
          · -- n < 143525179
            rcases Nat.lt_or_ge n 143345323 with hs5 | hs5
            · -- n < 143345323
              exact Brocard.berndt_galway_chunk_0797 n m (by omega) (by omega) h
            · -- n >= 143345323
              exact Brocard.berndt_galway_chunk_0798 n m (by omega) (by omega) h
          · -- n >= 143525179
            exact Brocard.berndt_galway_chunk_0799 n m (by omega) (by omega) h
        · -- n >= 143705035
          rcases Nat.lt_or_ge n 144064748 with hs4 | hs4
          · -- n < 144064748
            rcases Nat.lt_or_ge n 143884892 with hs5 | hs5
            · -- n < 143884892
              exact Brocard.berndt_galway_chunk_0800 n m (by omega) (by omega) h
            · -- n >= 143884892
              exact Brocard.berndt_galway_chunk_0801 n m (by omega) (by omega) h
          · -- n >= 144064748
            exact Brocard.berndt_galway_chunk_0802 n m (by omega) (by omega) h
    · -- n >= 144244604
      rcases Nat.lt_or_ge n 145323741 with hs2 | hs2
      · -- n < 145323741
        rcases Nat.lt_or_ge n 144784172 with hs3 | hs3
        · -- n < 144784172
          rcases Nat.lt_or_ge n 144604316 with hs4 | hs4
          · -- n < 144604316
            rcases Nat.lt_or_ge n 144424460 with hs5 | hs5
            · -- n < 144424460
              exact Brocard.berndt_galway_chunk_0803 n m (by omega) (by omega) h
            · -- n >= 144424460
              exact Brocard.berndt_galway_chunk_0804 n m (by omega) (by omega) h
          · -- n >= 144604316
            exact Brocard.berndt_galway_chunk_0805 n m (by omega) (by omega) h
        · -- n >= 144784172
          rcases Nat.lt_or_ge n 145143884 with hs4 | hs4
          · -- n < 145143884
            rcases Nat.lt_or_ge n 144964028 with hs5 | hs5
            · -- n < 144964028
              exact Brocard.berndt_galway_chunk_0806 n m (by omega) (by omega) h
            · -- n >= 144964028
              exact Brocard.berndt_galway_chunk_0807 n m (by omega) (by omega) h
          · -- n >= 145143884
            exact Brocard.berndt_galway_chunk_0808 n m (by omega) (by omega) h
      · -- n >= 145323741
        rcases Nat.lt_or_ge n 145863309 with hs3 | hs3
        · -- n < 145863309
          rcases Nat.lt_or_ge n 145683453 with hs4 | hs4
          · -- n < 145683453
            rcases Nat.lt_or_ge n 145503597 with hs5 | hs5
            · -- n < 145503597
              exact Brocard.berndt_galway_chunk_0809 n m (by omega) (by omega) h
            · -- n >= 145503597
              exact Brocard.berndt_galway_chunk_0810 n m (by omega) (by omega) h
          · -- n >= 145683453
            exact Brocard.berndt_galway_chunk_0811 n m (by omega) (by omega) h
        · -- n >= 145863309
          rcases Nat.lt_or_ge n 146043165 with hs4 | hs4
          · -- n < 146043165
            exact Brocard.berndt_galway_chunk_0812 n m (by omega) (by omega) h
          · -- n >= 146043165
            exact Brocard.berndt_galway_chunk_0813 n m (by omega) (by omega) h
  · -- n >= 146223021
    rcases Nat.lt_or_ge n 148381294 with hs1 | hs1
    · -- n < 148381294
      rcases Nat.lt_or_ge n 147302158 with hs2 | hs2
      · -- n < 147302158
        rcases Nat.lt_or_ge n 146762589 with hs3 | hs3
        · -- n < 146762589
          rcases Nat.lt_or_ge n 146582733 with hs4 | hs4
          · -- n < 146582733
            rcases Nat.lt_or_ge n 146402877 with hs5 | hs5
            · -- n < 146402877
              exact Brocard.berndt_galway_chunk_0814 n m (by omega) (by omega) h
            · -- n >= 146402877
              exact Brocard.berndt_galway_chunk_0815 n m (by omega) (by omega) h
          · -- n >= 146582733
            exact Brocard.berndt_galway_chunk_0816 n m (by omega) (by omega) h
        · -- n >= 146762589
          rcases Nat.lt_or_ge n 147122302 with hs4 | hs4
          · -- n < 147122302
            rcases Nat.lt_or_ge n 146942446 with hs5 | hs5
            · -- n < 146942446
              exact Brocard.berndt_galway_chunk_0817 n m (by omega) (by omega) h
            · -- n >= 146942446
              exact Brocard.berndt_galway_chunk_0818 n m (by omega) (by omega) h
          · -- n >= 147122302
            exact Brocard.berndt_galway_chunk_0819 n m (by omega) (by omega) h
      · -- n >= 147302158
        rcases Nat.lt_or_ge n 147841726 with hs3 | hs3
        · -- n < 147841726
          rcases Nat.lt_or_ge n 147661870 with hs4 | hs4
          · -- n < 147661870
            rcases Nat.lt_or_ge n 147482014 with hs5 | hs5
            · -- n < 147482014
              exact Brocard.berndt_galway_chunk_0820 n m (by omega) (by omega) h
            · -- n >= 147482014
              exact Brocard.berndt_galway_chunk_0821 n m (by omega) (by omega) h
          · -- n >= 147661870
            exact Brocard.berndt_galway_chunk_0822 n m (by omega) (by omega) h
        · -- n >= 147841726
          rcases Nat.lt_or_ge n 148201438 with hs4 | hs4
          · -- n < 148201438
            rcases Nat.lt_or_ge n 148021582 with hs5 | hs5
            · -- n < 148021582
              exact Brocard.berndt_galway_chunk_0823 n m (by omega) (by omega) h
            · -- n >= 148021582
              exact Brocard.berndt_galway_chunk_0824 n m (by omega) (by omega) h
          · -- n >= 148201438
            exact Brocard.berndt_galway_chunk_0825 n m (by omega) (by omega) h
    · -- n >= 148381294
      rcases Nat.lt_or_ge n 149460431 with hs2 | hs2
      · -- n < 149460431
        rcases Nat.lt_or_ge n 148920863 with hs3 | hs3
        · -- n < 148920863
          rcases Nat.lt_or_ge n 148741007 with hs4 | hs4
          · -- n < 148741007
            rcases Nat.lt_or_ge n 148561151 with hs5 | hs5
            · -- n < 148561151
              exact Brocard.berndt_galway_chunk_0826 n m (by omega) (by omega) h
            · -- n >= 148561151
              exact Brocard.berndt_galway_chunk_0827 n m (by omega) (by omega) h
          · -- n >= 148741007
            exact Brocard.berndt_galway_chunk_0828 n m (by omega) (by omega) h
        · -- n >= 148920863
          rcases Nat.lt_or_ge n 149280575 with hs4 | hs4
          · -- n < 149280575
            rcases Nat.lt_or_ge n 149100719 with hs5 | hs5
            · -- n < 149100719
              exact Brocard.berndt_galway_chunk_0829 n m (by omega) (by omega) h
            · -- n >= 149100719
              exact Brocard.berndt_galway_chunk_0830 n m (by omega) (by omega) h
          · -- n >= 149280575
            exact Brocard.berndt_galway_chunk_0831 n m (by omega) (by omega) h
      · -- n >= 149460431
        rcases Nat.lt_or_ge n 150000000 with hs3 | hs3
        · -- n < 150000000
          rcases Nat.lt_or_ge n 149820143 with hs4 | hs4
          · -- n < 149820143
            rcases Nat.lt_or_ge n 149640287 with hs5 | hs5
            · -- n < 149640287
              exact Brocard.berndt_galway_chunk_0832 n m (by omega) (by omega) h
            · -- n >= 149640287
              exact Brocard.berndt_galway_chunk_0833 n m (by omega) (by omega) h
          · -- n >= 149820143
            exact Brocard.berndt_galway_chunk_0834 n m (by omega) (by omega) h
        · -- n >= 150000000
          rcases Nat.lt_or_ge n 150179856 with hs4 | hs4
          · -- n < 150179856
            exact Brocard.berndt_galway_chunk_0835 n m (by omega) (by omega) h
          · -- n >= 150179856
            exact Brocard.berndt_galway_chunk_0836 n m (by omega) (by omega) h
