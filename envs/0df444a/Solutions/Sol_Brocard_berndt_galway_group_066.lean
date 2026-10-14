-- Prove2me | solution 1 for Brocard.berndt_galway_group_066
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:41:28.218064+00:00
-- url     : https://prove2.me/submissions/39394ddc-140d-4012-9dfd-d3c21b65e493

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_3015
import Theorems.Thm_Brocard_berndt_galway_chunk_3016
import Theorems.Thm_Brocard_berndt_galway_chunk_3017
import Theorems.Thm_Brocard_berndt_galway_chunk_3018
import Theorems.Thm_Brocard_berndt_galway_chunk_3019
import Theorems.Thm_Brocard_berndt_galway_chunk_3020
import Theorems.Thm_Brocard_berndt_galway_chunk_3021
import Theorems.Thm_Brocard_berndt_galway_chunk_3022
import Theorems.Thm_Brocard_berndt_galway_chunk_3023
import Theorems.Thm_Brocard_berndt_galway_chunk_3024
import Theorems.Thm_Brocard_berndt_galway_chunk_3025
import Theorems.Thm_Brocard_berndt_galway_chunk_3026
import Theorems.Thm_Brocard_berndt_galway_chunk_3027
import Theorems.Thm_Brocard_berndt_galway_chunk_3028
import Theorems.Thm_Brocard_berndt_galway_chunk_3029
import Theorems.Thm_Brocard_berndt_galway_chunk_3030
import Theorems.Thm_Brocard_berndt_galway_chunk_3031
import Theorems.Thm_Brocard_berndt_galway_chunk_3032
import Theorems.Thm_Brocard_berndt_galway_chunk_3033
import Theorems.Thm_Brocard_berndt_galway_chunk_3034
import Theorems.Thm_Brocard_berndt_galway_chunk_3035
import Theorems.Thm_Brocard_berndt_galway_chunk_3036
import Theorems.Thm_Brocard_berndt_galway_chunk_3037
import Theorems.Thm_Brocard_berndt_galway_chunk_3038
import Theorems.Thm_Brocard_berndt_galway_chunk_3039
import Theorems.Thm_Brocard_berndt_galway_chunk_3040
import Theorems.Thm_Brocard_berndt_galway_chunk_3041
import Theorems.Thm_Brocard_berndt_galway_chunk_3042
import Theorems.Thm_Brocard_berndt_galway_chunk_3043
import Theorems.Thm_Brocard_berndt_galway_chunk_3044
import Theorems.Thm_Brocard_berndt_galway_chunk_3045
import Theorems.Thm_Brocard_berndt_galway_chunk_3046
import Theorems.Thm_Brocard_berndt_galway_chunk_3047
import Theorems.Thm_Brocard_berndt_galway_chunk_3048
import Theorems.Thm_Brocard_berndt_galway_chunk_3049
import Theorems.Thm_Brocard_berndt_galway_chunk_3050
import Theorems.Thm_Brocard_berndt_galway_chunk_3051
import Theorems.Thm_Brocard_berndt_galway_chunk_3052
import Theorems.Thm_Brocard_berndt_galway_chunk_3053
import Theorems.Thm_Brocard_berndt_galway_chunk_3054
import Theorems.Thm_Brocard_berndt_galway_chunk_3055
import Theorems.Thm_Brocard_berndt_galway_chunk_3056
import Theorems.Thm_Brocard_berndt_galway_chunk_3057
import Theorems.Thm_Brocard_berndt_galway_chunk_3058
import Theorems.Thm_Brocard_berndt_galway_chunk_3059
import Theorems.Thm_Brocard_berndt_galway_chunk_3060

theorem solution (n m : ℕ) (h1 : 542086330 ≤ n) (h2 : n < 550359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 546223021 with hs0 | hs0
  · -- n < 546223021
    rcases Nat.lt_or_ge n 544244604 with hs1 | hs1
    · -- n < 544244604
      rcases Nat.lt_or_ge n 543165467 with hs2 | hs2
      · -- n < 543165467
        rcases Nat.lt_or_ge n 542625899 with hs3 | hs3
        · -- n < 542625899
          rcases Nat.lt_or_ge n 542446043 with hs4 | hs4
          · -- n < 542446043
            rcases Nat.lt_or_ge n 542266187 with hs5 | hs5
            · -- n < 542266187
              exact Brocard.berndt_galway_chunk_3015 n m (by omega) (by omega) h
            · -- n >= 542266187
              exact Brocard.berndt_galway_chunk_3016 n m (by omega) (by omega) h
          · -- n >= 542446043
            exact Brocard.berndt_galway_chunk_3017 n m (by omega) (by omega) h
        · -- n >= 542625899
          rcases Nat.lt_or_ge n 542985611 with hs4 | hs4
          · -- n < 542985611
            rcases Nat.lt_or_ge n 542805755 with hs5 | hs5
            · -- n < 542805755
              exact Brocard.berndt_galway_chunk_3018 n m (by omega) (by omega) h
            · -- n >= 542805755
              exact Brocard.berndt_galway_chunk_3019 n m (by omega) (by omega) h
          · -- n >= 542985611
            exact Brocard.berndt_galway_chunk_3020 n m (by omega) (by omega) h
      · -- n >= 543165467
        rcases Nat.lt_or_ge n 543705035 with hs3 | hs3
        · -- n < 543705035
          rcases Nat.lt_or_ge n 543525179 with hs4 | hs4
          · -- n < 543525179
            rcases Nat.lt_or_ge n 543345323 with hs5 | hs5
            · -- n < 543345323
              exact Brocard.berndt_galway_chunk_3021 n m (by omega) (by omega) h
            · -- n >= 543345323
              exact Brocard.berndt_galway_chunk_3022 n m (by omega) (by omega) h
          · -- n >= 543525179
            exact Brocard.berndt_galway_chunk_3023 n m (by omega) (by omega) h
        · -- n >= 543705035
          rcases Nat.lt_or_ge n 544064748 with hs4 | hs4
          · -- n < 544064748
            rcases Nat.lt_or_ge n 543884892 with hs5 | hs5
            · -- n < 543884892
              exact Brocard.berndt_galway_chunk_3024 n m (by omega) (by omega) h
            · -- n >= 543884892
              exact Brocard.berndt_galway_chunk_3025 n m (by omega) (by omega) h
          · -- n >= 544064748
            exact Brocard.berndt_galway_chunk_3026 n m (by omega) (by omega) h
    · -- n >= 544244604
      rcases Nat.lt_or_ge n 545323741 with hs2 | hs2
      · -- n < 545323741
        rcases Nat.lt_or_ge n 544784172 with hs3 | hs3
        · -- n < 544784172
          rcases Nat.lt_or_ge n 544604316 with hs4 | hs4
          · -- n < 544604316
            rcases Nat.lt_or_ge n 544424460 with hs5 | hs5
            · -- n < 544424460
              exact Brocard.berndt_galway_chunk_3027 n m (by omega) (by omega) h
            · -- n >= 544424460
              exact Brocard.berndt_galway_chunk_3028 n m (by omega) (by omega) h
          · -- n >= 544604316
            exact Brocard.berndt_galway_chunk_3029 n m (by omega) (by omega) h
        · -- n >= 544784172
          rcases Nat.lt_or_ge n 545143884 with hs4 | hs4
          · -- n < 545143884
            rcases Nat.lt_or_ge n 544964028 with hs5 | hs5
            · -- n < 544964028
              exact Brocard.berndt_galway_chunk_3030 n m (by omega) (by omega) h
            · -- n >= 544964028
              exact Brocard.berndt_galway_chunk_3031 n m (by omega) (by omega) h
          · -- n >= 545143884
            exact Brocard.berndt_galway_chunk_3032 n m (by omega) (by omega) h
      · -- n >= 545323741
        rcases Nat.lt_or_ge n 545863309 with hs3 | hs3
        · -- n < 545863309
          rcases Nat.lt_or_ge n 545683453 with hs4 | hs4
          · -- n < 545683453
            rcases Nat.lt_or_ge n 545503597 with hs5 | hs5
            · -- n < 545503597
              exact Brocard.berndt_galway_chunk_3033 n m (by omega) (by omega) h
            · -- n >= 545503597
              exact Brocard.berndt_galway_chunk_3034 n m (by omega) (by omega) h
          · -- n >= 545683453
            exact Brocard.berndt_galway_chunk_3035 n m (by omega) (by omega) h
        · -- n >= 545863309
          rcases Nat.lt_or_ge n 546043165 with hs4 | hs4
          · -- n < 546043165
            exact Brocard.berndt_galway_chunk_3036 n m (by omega) (by omega) h
          · -- n >= 546043165
            exact Brocard.berndt_galway_chunk_3037 n m (by omega) (by omega) h
  · -- n >= 546223021
    rcases Nat.lt_or_ge n 548381294 with hs1 | hs1
    · -- n < 548381294
      rcases Nat.lt_or_ge n 547302158 with hs2 | hs2
      · -- n < 547302158
        rcases Nat.lt_or_ge n 546762589 with hs3 | hs3
        · -- n < 546762589
          rcases Nat.lt_or_ge n 546582733 with hs4 | hs4
          · -- n < 546582733
            rcases Nat.lt_or_ge n 546402877 with hs5 | hs5
            · -- n < 546402877
              exact Brocard.berndt_galway_chunk_3038 n m (by omega) (by omega) h
            · -- n >= 546402877
              exact Brocard.berndt_galway_chunk_3039 n m (by omega) (by omega) h
          · -- n >= 546582733
            exact Brocard.berndt_galway_chunk_3040 n m (by omega) (by omega) h
        · -- n >= 546762589
          rcases Nat.lt_or_ge n 547122302 with hs4 | hs4
          · -- n < 547122302
            rcases Nat.lt_or_ge n 546942446 with hs5 | hs5
            · -- n < 546942446
              exact Brocard.berndt_galway_chunk_3041 n m (by omega) (by omega) h
            · -- n >= 546942446
              exact Brocard.berndt_galway_chunk_3042 n m (by omega) (by omega) h
          · -- n >= 547122302
            exact Brocard.berndt_galway_chunk_3043 n m (by omega) (by omega) h
      · -- n >= 547302158
        rcases Nat.lt_or_ge n 547841726 with hs3 | hs3
        · -- n < 547841726
          rcases Nat.lt_or_ge n 547661870 with hs4 | hs4
          · -- n < 547661870
            rcases Nat.lt_or_ge n 547482014 with hs5 | hs5
            · -- n < 547482014
              exact Brocard.berndt_galway_chunk_3044 n m (by omega) (by omega) h
            · -- n >= 547482014
              exact Brocard.berndt_galway_chunk_3045 n m (by omega) (by omega) h
          · -- n >= 547661870
            exact Brocard.berndt_galway_chunk_3046 n m (by omega) (by omega) h
        · -- n >= 547841726
          rcases Nat.lt_or_ge n 548201438 with hs4 | hs4
          · -- n < 548201438
            rcases Nat.lt_or_ge n 548021582 with hs5 | hs5
            · -- n < 548021582
              exact Brocard.berndt_galway_chunk_3047 n m (by omega) (by omega) h
            · -- n >= 548021582
              exact Brocard.berndt_galway_chunk_3048 n m (by omega) (by omega) h
          · -- n >= 548201438
            exact Brocard.berndt_galway_chunk_3049 n m (by omega) (by omega) h
    · -- n >= 548381294
      rcases Nat.lt_or_ge n 549460431 with hs2 | hs2
      · -- n < 549460431
        rcases Nat.lt_or_ge n 548920863 with hs3 | hs3
        · -- n < 548920863
          rcases Nat.lt_or_ge n 548741007 with hs4 | hs4
          · -- n < 548741007
            rcases Nat.lt_or_ge n 548561151 with hs5 | hs5
            · -- n < 548561151
              exact Brocard.berndt_galway_chunk_3050 n m (by omega) (by omega) h
            · -- n >= 548561151
              exact Brocard.berndt_galway_chunk_3051 n m (by omega) (by omega) h
          · -- n >= 548741007
            exact Brocard.berndt_galway_chunk_3052 n m (by omega) (by omega) h
        · -- n >= 548920863
          rcases Nat.lt_or_ge n 549280575 with hs4 | hs4
          · -- n < 549280575
            rcases Nat.lt_or_ge n 549100719 with hs5 | hs5
            · -- n < 549100719
              exact Brocard.berndt_galway_chunk_3053 n m (by omega) (by omega) h
            · -- n >= 549100719
              exact Brocard.berndt_galway_chunk_3054 n m (by omega) (by omega) h
          · -- n >= 549280575
            exact Brocard.berndt_galway_chunk_3055 n m (by omega) (by omega) h
      · -- n >= 549460431
        rcases Nat.lt_or_ge n 550000000 with hs3 | hs3
        · -- n < 550000000
          rcases Nat.lt_or_ge n 549820143 with hs4 | hs4
          · -- n < 549820143
            rcases Nat.lt_or_ge n 549640287 with hs5 | hs5
            · -- n < 549640287
              exact Brocard.berndt_galway_chunk_3056 n m (by omega) (by omega) h
            · -- n >= 549640287
              exact Brocard.berndt_galway_chunk_3057 n m (by omega) (by omega) h
          · -- n >= 549820143
            exact Brocard.berndt_galway_chunk_3058 n m (by omega) (by omega) h
        · -- n >= 550000000
          rcases Nat.lt_or_ge n 550179856 with hs4 | hs4
          · -- n < 550179856
            exact Brocard.berndt_galway_chunk_3059 n m (by omega) (by omega) h
          · -- n >= 550179856
            exact Brocard.berndt_galway_chunk_3060 n m (by omega) (by omega) h
