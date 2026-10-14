-- Prove2me | solution 1 for Brocard.berndt_galway_group_069
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:02:56.162866+00:00
-- url     : https://prove2.me/submissions/5328a637-d73b-4cf5-83cd-1ebddbb47d20

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_3153
import Theorems.Thm_Brocard_berndt_galway_chunk_3154
import Theorems.Thm_Brocard_berndt_galway_chunk_3155
import Theorems.Thm_Brocard_berndt_galway_chunk_3156
import Theorems.Thm_Brocard_berndt_galway_chunk_3157
import Theorems.Thm_Brocard_berndt_galway_chunk_3158
import Theorems.Thm_Brocard_berndt_galway_chunk_3159
import Theorems.Thm_Brocard_berndt_galway_chunk_3160
import Theorems.Thm_Brocard_berndt_galway_chunk_3161
import Theorems.Thm_Brocard_berndt_galway_chunk_3162
import Theorems.Thm_Brocard_berndt_galway_chunk_3163
import Theorems.Thm_Brocard_berndt_galway_chunk_3164
import Theorems.Thm_Brocard_berndt_galway_chunk_3165
import Theorems.Thm_Brocard_berndt_galway_chunk_3166
import Theorems.Thm_Brocard_berndt_galway_chunk_3167
import Theorems.Thm_Brocard_berndt_galway_chunk_3168
import Theorems.Thm_Brocard_berndt_galway_chunk_3169
import Theorems.Thm_Brocard_berndt_galway_chunk_3170
import Theorems.Thm_Brocard_berndt_galway_chunk_3171
import Theorems.Thm_Brocard_berndt_galway_chunk_3172
import Theorems.Thm_Brocard_berndt_galway_chunk_3173
import Theorems.Thm_Brocard_berndt_galway_chunk_3174
import Theorems.Thm_Brocard_berndt_galway_chunk_3175
import Theorems.Thm_Brocard_berndt_galway_chunk_3176
import Theorems.Thm_Brocard_berndt_galway_chunk_3177
import Theorems.Thm_Brocard_berndt_galway_chunk_3178
import Theorems.Thm_Brocard_berndt_galway_chunk_3179
import Theorems.Thm_Brocard_berndt_galway_chunk_3180
import Theorems.Thm_Brocard_berndt_galway_chunk_3181
import Theorems.Thm_Brocard_berndt_galway_chunk_3182
import Theorems.Thm_Brocard_berndt_galway_chunk_3183
import Theorems.Thm_Brocard_berndt_galway_chunk_3184
import Theorems.Thm_Brocard_berndt_galway_chunk_3185
import Theorems.Thm_Brocard_berndt_galway_chunk_3186
import Theorems.Thm_Brocard_berndt_galway_chunk_3187
import Theorems.Thm_Brocard_berndt_galway_chunk_3188
import Theorems.Thm_Brocard_berndt_galway_chunk_3189
import Theorems.Thm_Brocard_berndt_galway_chunk_3190
import Theorems.Thm_Brocard_berndt_galway_chunk_3191
import Theorems.Thm_Brocard_berndt_galway_chunk_3192
import Theorems.Thm_Brocard_berndt_galway_chunk_3193
import Theorems.Thm_Brocard_berndt_galway_chunk_3194
import Theorems.Thm_Brocard_berndt_galway_chunk_3195
import Theorems.Thm_Brocard_berndt_galway_chunk_3196
import Theorems.Thm_Brocard_berndt_galway_chunk_3197
import Theorems.Thm_Brocard_berndt_galway_chunk_3198

theorem solution (n m : ℕ) (h1 : 566906474 ≤ n) (h2 : n < 575179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 571043165 with hs0 | hs0
  · -- n < 571043165
    rcases Nat.lt_or_ge n 569064748 with hs1 | hs1
    · -- n < 569064748
      rcases Nat.lt_or_ge n 567985611 with hs2 | hs2
      · -- n < 567985611
        rcases Nat.lt_or_ge n 567446043 with hs3 | hs3
        · -- n < 567446043
          rcases Nat.lt_or_ge n 567266187 with hs4 | hs4
          · -- n < 567266187
            rcases Nat.lt_or_ge n 567086330 with hs5 | hs5
            · -- n < 567086330
              exact Brocard.berndt_galway_chunk_3153 n m (by omega) (by omega) h
            · -- n >= 567086330
              exact Brocard.berndt_galway_chunk_3154 n m (by omega) (by omega) h
          · -- n >= 567266187
            exact Brocard.berndt_galway_chunk_3155 n m (by omega) (by omega) h
        · -- n >= 567446043
          rcases Nat.lt_or_ge n 567805755 with hs4 | hs4
          · -- n < 567805755
            rcases Nat.lt_or_ge n 567625899 with hs5 | hs5
            · -- n < 567625899
              exact Brocard.berndt_galway_chunk_3156 n m (by omega) (by omega) h
            · -- n >= 567625899
              exact Brocard.berndt_galway_chunk_3157 n m (by omega) (by omega) h
          · -- n >= 567805755
            exact Brocard.berndt_galway_chunk_3158 n m (by omega) (by omega) h
      · -- n >= 567985611
        rcases Nat.lt_or_ge n 568525179 with hs3 | hs3
        · -- n < 568525179
          rcases Nat.lt_or_ge n 568345323 with hs4 | hs4
          · -- n < 568345323
            rcases Nat.lt_or_ge n 568165467 with hs5 | hs5
            · -- n < 568165467
              exact Brocard.berndt_galway_chunk_3159 n m (by omega) (by omega) h
            · -- n >= 568165467
              exact Brocard.berndt_galway_chunk_3160 n m (by omega) (by omega) h
          · -- n >= 568345323
            exact Brocard.berndt_galway_chunk_3161 n m (by omega) (by omega) h
        · -- n >= 568525179
          rcases Nat.lt_or_ge n 568884892 with hs4 | hs4
          · -- n < 568884892
            rcases Nat.lt_or_ge n 568705035 with hs5 | hs5
            · -- n < 568705035
              exact Brocard.berndt_galway_chunk_3162 n m (by omega) (by omega) h
            · -- n >= 568705035
              exact Brocard.berndt_galway_chunk_3163 n m (by omega) (by omega) h
          · -- n >= 568884892
            exact Brocard.berndt_galway_chunk_3164 n m (by omega) (by omega) h
    · -- n >= 569064748
      rcases Nat.lt_or_ge n 570143884 with hs2 | hs2
      · -- n < 570143884
        rcases Nat.lt_or_ge n 569604316 with hs3 | hs3
        · -- n < 569604316
          rcases Nat.lt_or_ge n 569424460 with hs4 | hs4
          · -- n < 569424460
            rcases Nat.lt_or_ge n 569244604 with hs5 | hs5
            · -- n < 569244604
              exact Brocard.berndt_galway_chunk_3165 n m (by omega) (by omega) h
            · -- n >= 569244604
              exact Brocard.berndt_galway_chunk_3166 n m (by omega) (by omega) h
          · -- n >= 569424460
            exact Brocard.berndt_galway_chunk_3167 n m (by omega) (by omega) h
        · -- n >= 569604316
          rcases Nat.lt_or_ge n 569964028 with hs4 | hs4
          · -- n < 569964028
            rcases Nat.lt_or_ge n 569784172 with hs5 | hs5
            · -- n < 569784172
              exact Brocard.berndt_galway_chunk_3168 n m (by omega) (by omega) h
            · -- n >= 569784172
              exact Brocard.berndt_galway_chunk_3169 n m (by omega) (by omega) h
          · -- n >= 569964028
            exact Brocard.berndt_galway_chunk_3170 n m (by omega) (by omega) h
      · -- n >= 570143884
        rcases Nat.lt_or_ge n 570683453 with hs3 | hs3
        · -- n < 570683453
          rcases Nat.lt_or_ge n 570503597 with hs4 | hs4
          · -- n < 570503597
            rcases Nat.lt_or_ge n 570323741 with hs5 | hs5
            · -- n < 570323741
              exact Brocard.berndt_galway_chunk_3171 n m (by omega) (by omega) h
            · -- n >= 570323741
              exact Brocard.berndt_galway_chunk_3172 n m (by omega) (by omega) h
          · -- n >= 570503597
            exact Brocard.berndt_galway_chunk_3173 n m (by omega) (by omega) h
        · -- n >= 570683453
          rcases Nat.lt_or_ge n 570863309 with hs4 | hs4
          · -- n < 570863309
            exact Brocard.berndt_galway_chunk_3174 n m (by omega) (by omega) h
          · -- n >= 570863309
            exact Brocard.berndt_galway_chunk_3175 n m (by omega) (by omega) h
  · -- n >= 571043165
    rcases Nat.lt_or_ge n 573201438 with hs1 | hs1
    · -- n < 573201438
      rcases Nat.lt_or_ge n 572122302 with hs2 | hs2
      · -- n < 572122302
        rcases Nat.lt_or_ge n 571582733 with hs3 | hs3
        · -- n < 571582733
          rcases Nat.lt_or_ge n 571402877 with hs4 | hs4
          · -- n < 571402877
            rcases Nat.lt_or_ge n 571223021 with hs5 | hs5
            · -- n < 571223021
              exact Brocard.berndt_galway_chunk_3176 n m (by omega) (by omega) h
            · -- n >= 571223021
              exact Brocard.berndt_galway_chunk_3177 n m (by omega) (by omega) h
          · -- n >= 571402877
            exact Brocard.berndt_galway_chunk_3178 n m (by omega) (by omega) h
        · -- n >= 571582733
          rcases Nat.lt_or_ge n 571942446 with hs4 | hs4
          · -- n < 571942446
            rcases Nat.lt_or_ge n 571762589 with hs5 | hs5
            · -- n < 571762589
              exact Brocard.berndt_galway_chunk_3179 n m (by omega) (by omega) h
            · -- n >= 571762589
              exact Brocard.berndt_galway_chunk_3180 n m (by omega) (by omega) h
          · -- n >= 571942446
            exact Brocard.berndt_galway_chunk_3181 n m (by omega) (by omega) h
      · -- n >= 572122302
        rcases Nat.lt_or_ge n 572661870 with hs3 | hs3
        · -- n < 572661870
          rcases Nat.lt_or_ge n 572482014 with hs4 | hs4
          · -- n < 572482014
            rcases Nat.lt_or_ge n 572302158 with hs5 | hs5
            · -- n < 572302158
              exact Brocard.berndt_galway_chunk_3182 n m (by omega) (by omega) h
            · -- n >= 572302158
              exact Brocard.berndt_galway_chunk_3183 n m (by omega) (by omega) h
          · -- n >= 572482014
            exact Brocard.berndt_galway_chunk_3184 n m (by omega) (by omega) h
        · -- n >= 572661870
          rcases Nat.lt_or_ge n 573021582 with hs4 | hs4
          · -- n < 573021582
            rcases Nat.lt_or_ge n 572841726 with hs5 | hs5
            · -- n < 572841726
              exact Brocard.berndt_galway_chunk_3185 n m (by omega) (by omega) h
            · -- n >= 572841726
              exact Brocard.berndt_galway_chunk_3186 n m (by omega) (by omega) h
          · -- n >= 573021582
            exact Brocard.berndt_galway_chunk_3187 n m (by omega) (by omega) h
    · -- n >= 573201438
      rcases Nat.lt_or_ge n 574280575 with hs2 | hs2
      · -- n < 574280575
        rcases Nat.lt_or_ge n 573741007 with hs3 | hs3
        · -- n < 573741007
          rcases Nat.lt_or_ge n 573561151 with hs4 | hs4
          · -- n < 573561151
            rcases Nat.lt_or_ge n 573381294 with hs5 | hs5
            · -- n < 573381294
              exact Brocard.berndt_galway_chunk_3188 n m (by omega) (by omega) h
            · -- n >= 573381294
              exact Brocard.berndt_galway_chunk_3189 n m (by omega) (by omega) h
          · -- n >= 573561151
            exact Brocard.berndt_galway_chunk_3190 n m (by omega) (by omega) h
        · -- n >= 573741007
          rcases Nat.lt_or_ge n 574100719 with hs4 | hs4
          · -- n < 574100719
            rcases Nat.lt_or_ge n 573920863 with hs5 | hs5
            · -- n < 573920863
              exact Brocard.berndt_galway_chunk_3191 n m (by omega) (by omega) h
            · -- n >= 573920863
              exact Brocard.berndt_galway_chunk_3192 n m (by omega) (by omega) h
          · -- n >= 574100719
            exact Brocard.berndt_galway_chunk_3193 n m (by omega) (by omega) h
      · -- n >= 574280575
        rcases Nat.lt_or_ge n 574820143 with hs3 | hs3
        · -- n < 574820143
          rcases Nat.lt_or_ge n 574640287 with hs4 | hs4
          · -- n < 574640287
            rcases Nat.lt_or_ge n 574460431 with hs5 | hs5
            · -- n < 574460431
              exact Brocard.berndt_galway_chunk_3194 n m (by omega) (by omega) h
            · -- n >= 574460431
              exact Brocard.berndt_galway_chunk_3195 n m (by omega) (by omega) h
          · -- n >= 574640287
            exact Brocard.berndt_galway_chunk_3196 n m (by omega) (by omega) h
        · -- n >= 574820143
          rcases Nat.lt_or_ge n 575000000 with hs4 | hs4
          · -- n < 575000000
            exact Brocard.berndt_galway_chunk_3197 n m (by omega) (by omega) h
          · -- n >= 575000000
            exact Brocard.berndt_galway_chunk_3198 n m (by omega) (by omega) h
