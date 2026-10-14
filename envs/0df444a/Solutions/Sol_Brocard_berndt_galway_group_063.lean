-- Prove2me | solution 1 for Brocard.berndt_galway_group_063
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:15:24.839111+00:00
-- url     : https://prove2.me/submissions/8d839c09-13f6-42ae-b78d-9b0619456b2d

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_2875
import Theorems.Thm_Brocard_berndt_galway_chunk_2876
import Theorems.Thm_Brocard_berndt_galway_chunk_2877
import Theorems.Thm_Brocard_berndt_galway_chunk_2878
import Theorems.Thm_Brocard_berndt_galway_chunk_2879
import Theorems.Thm_Brocard_berndt_galway_chunk_2880
import Theorems.Thm_Brocard_berndt_galway_chunk_2881
import Theorems.Thm_Brocard_berndt_galway_chunk_2882
import Theorems.Thm_Brocard_berndt_galway_chunk_2883
import Theorems.Thm_Brocard_berndt_galway_chunk_2884
import Theorems.Thm_Brocard_berndt_galway_chunk_2885
import Theorems.Thm_Brocard_berndt_galway_chunk_2886
import Theorems.Thm_Brocard_berndt_galway_chunk_2887
import Theorems.Thm_Brocard_berndt_galway_chunk_2888
import Theorems.Thm_Brocard_berndt_galway_chunk_2889
import Theorems.Thm_Brocard_berndt_galway_chunk_2890
import Theorems.Thm_Brocard_berndt_galway_chunk_2891
import Theorems.Thm_Brocard_berndt_galway_chunk_2892
import Theorems.Thm_Brocard_berndt_galway_chunk_2893
import Theorems.Thm_Brocard_berndt_galway_chunk_2894
import Theorems.Thm_Brocard_berndt_galway_chunk_2895
import Theorems.Thm_Brocard_berndt_galway_chunk_2896
import Theorems.Thm_Brocard_berndt_galway_chunk_2897
import Theorems.Thm_Brocard_berndt_galway_chunk_2898
import Theorems.Thm_Brocard_berndt_galway_chunk_2899
import Theorems.Thm_Brocard_berndt_galway_chunk_2900
import Theorems.Thm_Brocard_berndt_galway_chunk_2901
import Theorems.Thm_Brocard_berndt_galway_chunk_2902
import Theorems.Thm_Brocard_berndt_galway_chunk_2903
import Theorems.Thm_Brocard_berndt_galway_chunk_2904
import Theorems.Thm_Brocard_berndt_galway_chunk_2905
import Theorems.Thm_Brocard_berndt_galway_chunk_2906
import Theorems.Thm_Brocard_berndt_galway_chunk_2907
import Theorems.Thm_Brocard_berndt_galway_chunk_2908
import Theorems.Thm_Brocard_berndt_galway_chunk_2909
import Theorems.Thm_Brocard_berndt_galway_chunk_2910
import Theorems.Thm_Brocard_berndt_galway_chunk_2911
import Theorems.Thm_Brocard_berndt_galway_chunk_2912
import Theorems.Thm_Brocard_berndt_galway_chunk_2913
import Theorems.Thm_Brocard_berndt_galway_chunk_2914
import Theorems.Thm_Brocard_berndt_galway_chunk_2915
import Theorems.Thm_Brocard_berndt_galway_chunk_2916
import Theorems.Thm_Brocard_berndt_galway_chunk_2917
import Theorems.Thm_Brocard_berndt_galway_chunk_2918
import Theorems.Thm_Brocard_berndt_galway_chunk_2919
import Theorems.Thm_Brocard_berndt_galway_chunk_2920
import Theorems.Thm_Brocard_berndt_galway_chunk_2921

theorem solution (n m : ℕ) (h1 : 516906474 ≤ n) (h2 : n < 525359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 521223021 with hs0 | hs0
  · -- n < 521223021
    rcases Nat.lt_or_ge n 519064748 with hs1 | hs1
    · -- n < 519064748
      rcases Nat.lt_or_ge n 517985611 with hs2 | hs2
      · -- n < 517985611
        rcases Nat.lt_or_ge n 517446043 with hs3 | hs3
        · -- n < 517446043
          rcases Nat.lt_or_ge n 517266187 with hs4 | hs4
          · -- n < 517266187
            rcases Nat.lt_or_ge n 517086330 with hs5 | hs5
            · -- n < 517086330
              exact Brocard.berndt_galway_chunk_2875 n m (by omega) (by omega) h
            · -- n >= 517086330
              exact Brocard.berndt_galway_chunk_2876 n m (by omega) (by omega) h
          · -- n >= 517266187
            exact Brocard.berndt_galway_chunk_2877 n m (by omega) (by omega) h
        · -- n >= 517446043
          rcases Nat.lt_or_ge n 517805755 with hs4 | hs4
          · -- n < 517805755
            rcases Nat.lt_or_ge n 517625899 with hs5 | hs5
            · -- n < 517625899
              exact Brocard.berndt_galway_chunk_2878 n m (by omega) (by omega) h
            · -- n >= 517625899
              exact Brocard.berndt_galway_chunk_2879 n m (by omega) (by omega) h
          · -- n >= 517805755
            exact Brocard.berndt_galway_chunk_2880 n m (by omega) (by omega) h
      · -- n >= 517985611
        rcases Nat.lt_or_ge n 518525179 with hs3 | hs3
        · -- n < 518525179
          rcases Nat.lt_or_ge n 518345323 with hs4 | hs4
          · -- n < 518345323
            rcases Nat.lt_or_ge n 518165467 with hs5 | hs5
            · -- n < 518165467
              exact Brocard.berndt_galway_chunk_2881 n m (by omega) (by omega) h
            · -- n >= 518165467
              exact Brocard.berndt_galway_chunk_2882 n m (by omega) (by omega) h
          · -- n >= 518345323
            exact Brocard.berndt_galway_chunk_2883 n m (by omega) (by omega) h
        · -- n >= 518525179
          rcases Nat.lt_or_ge n 518884892 with hs4 | hs4
          · -- n < 518884892
            rcases Nat.lt_or_ge n 518705035 with hs5 | hs5
            · -- n < 518705035
              exact Brocard.berndt_galway_chunk_2884 n m (by omega) (by omega) h
            · -- n >= 518705035
              exact Brocard.berndt_galway_chunk_2885 n m (by omega) (by omega) h
          · -- n >= 518884892
            exact Brocard.berndt_galway_chunk_2886 n m (by omega) (by omega) h
    · -- n >= 519064748
      rcases Nat.lt_or_ge n 520143884 with hs2 | hs2
      · -- n < 520143884
        rcases Nat.lt_or_ge n 519604316 with hs3 | hs3
        · -- n < 519604316
          rcases Nat.lt_or_ge n 519424460 with hs4 | hs4
          · -- n < 519424460
            rcases Nat.lt_or_ge n 519244604 with hs5 | hs5
            · -- n < 519244604
              exact Brocard.berndt_galway_chunk_2887 n m (by omega) (by omega) h
            · -- n >= 519244604
              exact Brocard.berndt_galway_chunk_2888 n m (by omega) (by omega) h
          · -- n >= 519424460
            exact Brocard.berndt_galway_chunk_2889 n m (by omega) (by omega) h
        · -- n >= 519604316
          rcases Nat.lt_or_ge n 519964028 with hs4 | hs4
          · -- n < 519964028
            rcases Nat.lt_or_ge n 519784172 with hs5 | hs5
            · -- n < 519784172
              exact Brocard.berndt_galway_chunk_2890 n m (by omega) (by omega) h
            · -- n >= 519784172
              exact Brocard.berndt_galway_chunk_2891 n m (by omega) (by omega) h
          · -- n >= 519964028
            exact Brocard.berndt_galway_chunk_2892 n m (by omega) (by omega) h
      · -- n >= 520143884
        rcases Nat.lt_or_ge n 520683453 with hs3 | hs3
        · -- n < 520683453
          rcases Nat.lt_or_ge n 520503597 with hs4 | hs4
          · -- n < 520503597
            rcases Nat.lt_or_ge n 520323741 with hs5 | hs5
            · -- n < 520323741
              exact Brocard.berndt_galway_chunk_2893 n m (by omega) (by omega) h
            · -- n >= 520323741
              exact Brocard.berndt_galway_chunk_2894 n m (by omega) (by omega) h
          · -- n >= 520503597
            exact Brocard.berndt_galway_chunk_2895 n m (by omega) (by omega) h
        · -- n >= 520683453
          rcases Nat.lt_or_ge n 521043165 with hs4 | hs4
          · -- n < 521043165
            rcases Nat.lt_or_ge n 520863309 with hs5 | hs5
            · -- n < 520863309
              exact Brocard.berndt_galway_chunk_2896 n m (by omega) (by omega) h
            · -- n >= 520863309
              exact Brocard.berndt_galway_chunk_2897 n m (by omega) (by omega) h
          · -- n >= 521043165
            exact Brocard.berndt_galway_chunk_2898 n m (by omega) (by omega) h
  · -- n >= 521223021
    rcases Nat.lt_or_ge n 523381294 with hs1 | hs1
    · -- n < 523381294
      rcases Nat.lt_or_ge n 522302158 with hs2 | hs2
      · -- n < 522302158
        rcases Nat.lt_or_ge n 521762589 with hs3 | hs3
        · -- n < 521762589
          rcases Nat.lt_or_ge n 521582733 with hs4 | hs4
          · -- n < 521582733
            rcases Nat.lt_or_ge n 521402877 with hs5 | hs5
            · -- n < 521402877
              exact Brocard.berndt_galway_chunk_2899 n m (by omega) (by omega) h
            · -- n >= 521402877
              exact Brocard.berndt_galway_chunk_2900 n m (by omega) (by omega) h
          · -- n >= 521582733
            exact Brocard.berndt_galway_chunk_2901 n m (by omega) (by omega) h
        · -- n >= 521762589
          rcases Nat.lt_or_ge n 522122302 with hs4 | hs4
          · -- n < 522122302
            rcases Nat.lt_or_ge n 521942446 with hs5 | hs5
            · -- n < 521942446
              exact Brocard.berndt_galway_chunk_2902 n m (by omega) (by omega) h
            · -- n >= 521942446
              exact Brocard.berndt_galway_chunk_2903 n m (by omega) (by omega) h
          · -- n >= 522122302
            exact Brocard.berndt_galway_chunk_2904 n m (by omega) (by omega) h
      · -- n >= 522302158
        rcases Nat.lt_or_ge n 522841726 with hs3 | hs3
        · -- n < 522841726
          rcases Nat.lt_or_ge n 522661870 with hs4 | hs4
          · -- n < 522661870
            rcases Nat.lt_or_ge n 522482014 with hs5 | hs5
            · -- n < 522482014
              exact Brocard.berndt_galway_chunk_2905 n m (by omega) (by omega) h
            · -- n >= 522482014
              exact Brocard.berndt_galway_chunk_2906 n m (by omega) (by omega) h
          · -- n >= 522661870
            exact Brocard.berndt_galway_chunk_2907 n m (by omega) (by omega) h
        · -- n >= 522841726
          rcases Nat.lt_or_ge n 523201438 with hs4 | hs4
          · -- n < 523201438
            rcases Nat.lt_or_ge n 523021582 with hs5 | hs5
            · -- n < 523021582
              exact Brocard.berndt_galway_chunk_2908 n m (by omega) (by omega) h
            · -- n >= 523021582
              exact Brocard.berndt_galway_chunk_2909 n m (by omega) (by omega) h
          · -- n >= 523201438
            exact Brocard.berndt_galway_chunk_2910 n m (by omega) (by omega) h
    · -- n >= 523381294
      rcases Nat.lt_or_ge n 524460431 with hs2 | hs2
      · -- n < 524460431
        rcases Nat.lt_or_ge n 523920863 with hs3 | hs3
        · -- n < 523920863
          rcases Nat.lt_or_ge n 523741007 with hs4 | hs4
          · -- n < 523741007
            rcases Nat.lt_or_ge n 523561151 with hs5 | hs5
            · -- n < 523561151
              exact Brocard.berndt_galway_chunk_2911 n m (by omega) (by omega) h
            · -- n >= 523561151
              exact Brocard.berndt_galway_chunk_2912 n m (by omega) (by omega) h
          · -- n >= 523741007
            exact Brocard.berndt_galway_chunk_2913 n m (by omega) (by omega) h
        · -- n >= 523920863
          rcases Nat.lt_or_ge n 524280575 with hs4 | hs4
          · -- n < 524280575
            rcases Nat.lt_or_ge n 524100719 with hs5 | hs5
            · -- n < 524100719
              exact Brocard.berndt_galway_chunk_2914 n m (by omega) (by omega) h
            · -- n >= 524100719
              exact Brocard.berndt_galway_chunk_2915 n m (by omega) (by omega) h
          · -- n >= 524280575
            exact Brocard.berndt_galway_chunk_2916 n m (by omega) (by omega) h
      · -- n >= 524460431
        rcases Nat.lt_or_ge n 525000000 with hs3 | hs3
        · -- n < 525000000
          rcases Nat.lt_or_ge n 524820143 with hs4 | hs4
          · -- n < 524820143
            rcases Nat.lt_or_ge n 524640287 with hs5 | hs5
            · -- n < 524640287
              exact Brocard.berndt_galway_chunk_2917 n m (by omega) (by omega) h
            · -- n >= 524640287
              exact Brocard.berndt_galway_chunk_2918 n m (by omega) (by omega) h
          · -- n >= 524820143
            exact Brocard.berndt_galway_chunk_2919 n m (by omega) (by omega) h
        · -- n >= 525000000
          rcases Nat.lt_or_ge n 525179856 with hs4 | hs4
          · -- n < 525179856
            exact Brocard.berndt_galway_chunk_2920 n m (by omega) (by omega) h
          · -- n >= 525179856
            exact Brocard.berndt_galway_chunk_2921 n m (by omega) (by omega) h
