-- Prove2me | solution 1 for Brocard.berndt_galway_group_090
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:54:18.393007+00:00
-- url     : https://prove2.me/submissions/2ca0f37b-e3b8-4c1d-9510-2470e30e96ee

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_4127
import Theorems.Thm_Brocard_berndt_galway_chunk_4128
import Theorems.Thm_Brocard_berndt_galway_chunk_4129
import Theorems.Thm_Brocard_berndt_galway_chunk_4130
import Theorems.Thm_Brocard_berndt_galway_chunk_4131
import Theorems.Thm_Brocard_berndt_galway_chunk_4132
import Theorems.Thm_Brocard_berndt_galway_chunk_4133
import Theorems.Thm_Brocard_berndt_galway_chunk_4134
import Theorems.Thm_Brocard_berndt_galway_chunk_4135
import Theorems.Thm_Brocard_berndt_galway_chunk_4136
import Theorems.Thm_Brocard_berndt_galway_chunk_4137
import Theorems.Thm_Brocard_berndt_galway_chunk_4138
import Theorems.Thm_Brocard_berndt_galway_chunk_4139
import Theorems.Thm_Brocard_berndt_galway_chunk_4140
import Theorems.Thm_Brocard_berndt_galway_chunk_4141
import Theorems.Thm_Brocard_berndt_galway_chunk_4142
import Theorems.Thm_Brocard_berndt_galway_chunk_4143
import Theorems.Thm_Brocard_berndt_galway_chunk_4144
import Theorems.Thm_Brocard_berndt_galway_chunk_4145
import Theorems.Thm_Brocard_berndt_galway_chunk_4146
import Theorems.Thm_Brocard_berndt_galway_chunk_4147
import Theorems.Thm_Brocard_berndt_galway_chunk_4148
import Theorems.Thm_Brocard_berndt_galway_chunk_4149
import Theorems.Thm_Brocard_berndt_galway_chunk_4150
import Theorems.Thm_Brocard_berndt_galway_chunk_4151
import Theorems.Thm_Brocard_berndt_galway_chunk_4152
import Theorems.Thm_Brocard_berndt_galway_chunk_4153
import Theorems.Thm_Brocard_berndt_galway_chunk_4154
import Theorems.Thm_Brocard_berndt_galway_chunk_4155
import Theorems.Thm_Brocard_berndt_galway_chunk_4156
import Theorems.Thm_Brocard_berndt_galway_chunk_4157
import Theorems.Thm_Brocard_berndt_galway_chunk_4158
import Theorems.Thm_Brocard_berndt_galway_chunk_4159
import Theorems.Thm_Brocard_berndt_galway_chunk_4160
import Theorems.Thm_Brocard_berndt_galway_chunk_4161
import Theorems.Thm_Brocard_berndt_galway_chunk_4162
import Theorems.Thm_Brocard_berndt_galway_chunk_4163
import Theorems.Thm_Brocard_berndt_galway_chunk_4164
import Theorems.Thm_Brocard_berndt_galway_chunk_4165
import Theorems.Thm_Brocard_berndt_galway_chunk_4166
import Theorems.Thm_Brocard_berndt_galway_chunk_4167
import Theorems.Thm_Brocard_berndt_galway_chunk_4168
import Theorems.Thm_Brocard_berndt_galway_chunk_4169
import Theorems.Thm_Brocard_berndt_galway_chunk_4170
import Theorems.Thm_Brocard_berndt_galway_chunk_4171
import Theorems.Thm_Brocard_berndt_galway_chunk_4172

theorem solution (n m : ℕ) (h1 : 742086330 ≤ n) (h2 : n < 750359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 746223021 with hs0 | hs0
  · -- n < 746223021
    rcases Nat.lt_or_ge n 744244604 with hs1 | hs1
    · -- n < 744244604
      rcases Nat.lt_or_ge n 743165467 with hs2 | hs2
      · -- n < 743165467
        rcases Nat.lt_or_ge n 742625899 with hs3 | hs3
        · -- n < 742625899
          rcases Nat.lt_or_ge n 742446043 with hs4 | hs4
          · -- n < 742446043
            rcases Nat.lt_or_ge n 742266187 with hs5 | hs5
            · -- n < 742266187
              exact Brocard.berndt_galway_chunk_4127 n m (by omega) (by omega) h
            · -- n >= 742266187
              exact Brocard.berndt_galway_chunk_4128 n m (by omega) (by omega) h
          · -- n >= 742446043
            exact Brocard.berndt_galway_chunk_4129 n m (by omega) (by omega) h
        · -- n >= 742625899
          rcases Nat.lt_or_ge n 742985611 with hs4 | hs4
          · -- n < 742985611
            rcases Nat.lt_or_ge n 742805755 with hs5 | hs5
            · -- n < 742805755
              exact Brocard.berndt_galway_chunk_4130 n m (by omega) (by omega) h
            · -- n >= 742805755
              exact Brocard.berndt_galway_chunk_4131 n m (by omega) (by omega) h
          · -- n >= 742985611
            exact Brocard.berndt_galway_chunk_4132 n m (by omega) (by omega) h
      · -- n >= 743165467
        rcases Nat.lt_or_ge n 743705035 with hs3 | hs3
        · -- n < 743705035
          rcases Nat.lt_or_ge n 743525179 with hs4 | hs4
          · -- n < 743525179
            rcases Nat.lt_or_ge n 743345323 with hs5 | hs5
            · -- n < 743345323
              exact Brocard.berndt_galway_chunk_4133 n m (by omega) (by omega) h
            · -- n >= 743345323
              exact Brocard.berndt_galway_chunk_4134 n m (by omega) (by omega) h
          · -- n >= 743525179
            exact Brocard.berndt_galway_chunk_4135 n m (by omega) (by omega) h
        · -- n >= 743705035
          rcases Nat.lt_or_ge n 744064748 with hs4 | hs4
          · -- n < 744064748
            rcases Nat.lt_or_ge n 743884892 with hs5 | hs5
            · -- n < 743884892
              exact Brocard.berndt_galway_chunk_4136 n m (by omega) (by omega) h
            · -- n >= 743884892
              exact Brocard.berndt_galway_chunk_4137 n m (by omega) (by omega) h
          · -- n >= 744064748
            exact Brocard.berndt_galway_chunk_4138 n m (by omega) (by omega) h
    · -- n >= 744244604
      rcases Nat.lt_or_ge n 745323741 with hs2 | hs2
      · -- n < 745323741
        rcases Nat.lt_or_ge n 744784172 with hs3 | hs3
        · -- n < 744784172
          rcases Nat.lt_or_ge n 744604316 with hs4 | hs4
          · -- n < 744604316
            rcases Nat.lt_or_ge n 744424460 with hs5 | hs5
            · -- n < 744424460
              exact Brocard.berndt_galway_chunk_4139 n m (by omega) (by omega) h
            · -- n >= 744424460
              exact Brocard.berndt_galway_chunk_4140 n m (by omega) (by omega) h
          · -- n >= 744604316
            exact Brocard.berndt_galway_chunk_4141 n m (by omega) (by omega) h
        · -- n >= 744784172
          rcases Nat.lt_or_ge n 745143884 with hs4 | hs4
          · -- n < 745143884
            rcases Nat.lt_or_ge n 744964028 with hs5 | hs5
            · -- n < 744964028
              exact Brocard.berndt_galway_chunk_4142 n m (by omega) (by omega) h
            · -- n >= 744964028
              exact Brocard.berndt_galway_chunk_4143 n m (by omega) (by omega) h
          · -- n >= 745143884
            exact Brocard.berndt_galway_chunk_4144 n m (by omega) (by omega) h
      · -- n >= 745323741
        rcases Nat.lt_or_ge n 745863309 with hs3 | hs3
        · -- n < 745863309
          rcases Nat.lt_or_ge n 745683453 with hs4 | hs4
          · -- n < 745683453
            rcases Nat.lt_or_ge n 745503597 with hs5 | hs5
            · -- n < 745503597
              exact Brocard.berndt_galway_chunk_4145 n m (by omega) (by omega) h
            · -- n >= 745503597
              exact Brocard.berndt_galway_chunk_4146 n m (by omega) (by omega) h
          · -- n >= 745683453
            exact Brocard.berndt_galway_chunk_4147 n m (by omega) (by omega) h
        · -- n >= 745863309
          rcases Nat.lt_or_ge n 746043165 with hs4 | hs4
          · -- n < 746043165
            exact Brocard.berndt_galway_chunk_4148 n m (by omega) (by omega) h
          · -- n >= 746043165
            exact Brocard.berndt_galway_chunk_4149 n m (by omega) (by omega) h
  · -- n >= 746223021
    rcases Nat.lt_or_ge n 748381294 with hs1 | hs1
    · -- n < 748381294
      rcases Nat.lt_or_ge n 747302158 with hs2 | hs2
      · -- n < 747302158
        rcases Nat.lt_or_ge n 746762589 with hs3 | hs3
        · -- n < 746762589
          rcases Nat.lt_or_ge n 746582733 with hs4 | hs4
          · -- n < 746582733
            rcases Nat.lt_or_ge n 746402877 with hs5 | hs5
            · -- n < 746402877
              exact Brocard.berndt_galway_chunk_4150 n m (by omega) (by omega) h
            · -- n >= 746402877
              exact Brocard.berndt_galway_chunk_4151 n m (by omega) (by omega) h
          · -- n >= 746582733
            exact Brocard.berndt_galway_chunk_4152 n m (by omega) (by omega) h
        · -- n >= 746762589
          rcases Nat.lt_or_ge n 747122302 with hs4 | hs4
          · -- n < 747122302
            rcases Nat.lt_or_ge n 746942446 with hs5 | hs5
            · -- n < 746942446
              exact Brocard.berndt_galway_chunk_4153 n m (by omega) (by omega) h
            · -- n >= 746942446
              exact Brocard.berndt_galway_chunk_4154 n m (by omega) (by omega) h
          · -- n >= 747122302
            exact Brocard.berndt_galway_chunk_4155 n m (by omega) (by omega) h
      · -- n >= 747302158
        rcases Nat.lt_or_ge n 747841726 with hs3 | hs3
        · -- n < 747841726
          rcases Nat.lt_or_ge n 747661870 with hs4 | hs4
          · -- n < 747661870
            rcases Nat.lt_or_ge n 747482014 with hs5 | hs5
            · -- n < 747482014
              exact Brocard.berndt_galway_chunk_4156 n m (by omega) (by omega) h
            · -- n >= 747482014
              exact Brocard.berndt_galway_chunk_4157 n m (by omega) (by omega) h
          · -- n >= 747661870
            exact Brocard.berndt_galway_chunk_4158 n m (by omega) (by omega) h
        · -- n >= 747841726
          rcases Nat.lt_or_ge n 748201438 with hs4 | hs4
          · -- n < 748201438
            rcases Nat.lt_or_ge n 748021582 with hs5 | hs5
            · -- n < 748021582
              exact Brocard.berndt_galway_chunk_4159 n m (by omega) (by omega) h
            · -- n >= 748021582
              exact Brocard.berndt_galway_chunk_4160 n m (by omega) (by omega) h
          · -- n >= 748201438
            exact Brocard.berndt_galway_chunk_4161 n m (by omega) (by omega) h
    · -- n >= 748381294
      rcases Nat.lt_or_ge n 749460431 with hs2 | hs2
      · -- n < 749460431
        rcases Nat.lt_or_ge n 748920863 with hs3 | hs3
        · -- n < 748920863
          rcases Nat.lt_or_ge n 748741007 with hs4 | hs4
          · -- n < 748741007
            rcases Nat.lt_or_ge n 748561151 with hs5 | hs5
            · -- n < 748561151
              exact Brocard.berndt_galway_chunk_4162 n m (by omega) (by omega) h
            · -- n >= 748561151
              exact Brocard.berndt_galway_chunk_4163 n m (by omega) (by omega) h
          · -- n >= 748741007
            exact Brocard.berndt_galway_chunk_4164 n m (by omega) (by omega) h
        · -- n >= 748920863
          rcases Nat.lt_or_ge n 749280575 with hs4 | hs4
          · -- n < 749280575
            rcases Nat.lt_or_ge n 749100719 with hs5 | hs5
            · -- n < 749100719
              exact Brocard.berndt_galway_chunk_4165 n m (by omega) (by omega) h
            · -- n >= 749100719
              exact Brocard.berndt_galway_chunk_4166 n m (by omega) (by omega) h
          · -- n >= 749280575
            exact Brocard.berndt_galway_chunk_4167 n m (by omega) (by omega) h
      · -- n >= 749460431
        rcases Nat.lt_or_ge n 750000000 with hs3 | hs3
        · -- n < 750000000
          rcases Nat.lt_or_ge n 749820143 with hs4 | hs4
          · -- n < 749820143
            rcases Nat.lt_or_ge n 749640287 with hs5 | hs5
            · -- n < 749640287
              exact Brocard.berndt_galway_chunk_4168 n m (by omega) (by omega) h
            · -- n >= 749640287
              exact Brocard.berndt_galway_chunk_4169 n m (by omega) (by omega) h
          · -- n >= 749820143
            exact Brocard.berndt_galway_chunk_4170 n m (by omega) (by omega) h
        · -- n >= 750000000
          rcases Nat.lt_or_ge n 750179856 with hs4 | hs4
          · -- n < 750179856
            exact Brocard.berndt_galway_chunk_4171 n m (by omega) (by omega) h
          · -- n >= 750179856
            exact Brocard.berndt_galway_chunk_4172 n m (by omega) (by omega) h
