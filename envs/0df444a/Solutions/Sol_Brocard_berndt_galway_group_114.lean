-- Prove2me | solution 1 for Brocard.berndt_galway_group_114
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:31:42.90583+00:00
-- url     : https://prove2.me/submissions/ea2dcd60-38ae-494f-8d9d-709da750ba5b

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_5239
import Theorems.Thm_Brocard_berndt_galway_chunk_5240
import Theorems.Thm_Brocard_berndt_galway_chunk_5241
import Theorems.Thm_Brocard_berndt_galway_chunk_5242
import Theorems.Thm_Brocard_berndt_galway_chunk_5243
import Theorems.Thm_Brocard_berndt_galway_chunk_5244
import Theorems.Thm_Brocard_berndt_galway_chunk_5245
import Theorems.Thm_Brocard_berndt_galway_chunk_5246
import Theorems.Thm_Brocard_berndt_galway_chunk_5247
import Theorems.Thm_Brocard_berndt_galway_chunk_5248
import Theorems.Thm_Brocard_berndt_galway_chunk_5249
import Theorems.Thm_Brocard_berndt_galway_chunk_5250
import Theorems.Thm_Brocard_berndt_galway_chunk_5251
import Theorems.Thm_Brocard_berndt_galway_chunk_5252
import Theorems.Thm_Brocard_berndt_galway_chunk_5253
import Theorems.Thm_Brocard_berndt_galway_chunk_5254
import Theorems.Thm_Brocard_berndt_galway_chunk_5255
import Theorems.Thm_Brocard_berndt_galway_chunk_5256
import Theorems.Thm_Brocard_berndt_galway_chunk_5257
import Theorems.Thm_Brocard_berndt_galway_chunk_5258
import Theorems.Thm_Brocard_berndt_galway_chunk_5259
import Theorems.Thm_Brocard_berndt_galway_chunk_5260
import Theorems.Thm_Brocard_berndt_galway_chunk_5261
import Theorems.Thm_Brocard_berndt_galway_chunk_5262
import Theorems.Thm_Brocard_berndt_galway_chunk_5263
import Theorems.Thm_Brocard_berndt_galway_chunk_5264
import Theorems.Thm_Brocard_berndt_galway_chunk_5265
import Theorems.Thm_Brocard_berndt_galway_chunk_5266
import Theorems.Thm_Brocard_berndt_galway_chunk_5267
import Theorems.Thm_Brocard_berndt_galway_chunk_5268
import Theorems.Thm_Brocard_berndt_galway_chunk_5269
import Theorems.Thm_Brocard_berndt_galway_chunk_5270
import Theorems.Thm_Brocard_berndt_galway_chunk_5271
import Theorems.Thm_Brocard_berndt_galway_chunk_5272
import Theorems.Thm_Brocard_berndt_galway_chunk_5273
import Theorems.Thm_Brocard_berndt_galway_chunk_5274
import Theorems.Thm_Brocard_berndt_galway_chunk_5275
import Theorems.Thm_Brocard_berndt_galway_chunk_5276
import Theorems.Thm_Brocard_berndt_galway_chunk_5277
import Theorems.Thm_Brocard_berndt_galway_chunk_5278
import Theorems.Thm_Brocard_berndt_galway_chunk_5279
import Theorems.Thm_Brocard_berndt_galway_chunk_5280
import Theorems.Thm_Brocard_berndt_galway_chunk_5281
import Theorems.Thm_Brocard_berndt_galway_chunk_5282
import Theorems.Thm_Brocard_berndt_galway_chunk_5283
import Theorems.Thm_Brocard_berndt_galway_chunk_5284

theorem solution (n m : ℕ) (h1 : 942086330 ≤ n) (h2 : n < 950359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 946223021 with hs0 | hs0
  · -- n < 946223021
    rcases Nat.lt_or_ge n 944244604 with hs1 | hs1
    · -- n < 944244604
      rcases Nat.lt_or_ge n 943165467 with hs2 | hs2
      · -- n < 943165467
        rcases Nat.lt_or_ge n 942625899 with hs3 | hs3
        · -- n < 942625899
          rcases Nat.lt_or_ge n 942446043 with hs4 | hs4
          · -- n < 942446043
            rcases Nat.lt_or_ge n 942266187 with hs5 | hs5
            · -- n < 942266187
              exact Brocard.berndt_galway_chunk_5239 n m (by omega) (by omega) h
            · -- n >= 942266187
              exact Brocard.berndt_galway_chunk_5240 n m (by omega) (by omega) h
          · -- n >= 942446043
            exact Brocard.berndt_galway_chunk_5241 n m (by omega) (by omega) h
        · -- n >= 942625899
          rcases Nat.lt_or_ge n 942985611 with hs4 | hs4
          · -- n < 942985611
            rcases Nat.lt_or_ge n 942805755 with hs5 | hs5
            · -- n < 942805755
              exact Brocard.berndt_galway_chunk_5242 n m (by omega) (by omega) h
            · -- n >= 942805755
              exact Brocard.berndt_galway_chunk_5243 n m (by omega) (by omega) h
          · -- n >= 942985611
            exact Brocard.berndt_galway_chunk_5244 n m (by omega) (by omega) h
      · -- n >= 943165467
        rcases Nat.lt_or_ge n 943705035 with hs3 | hs3
        · -- n < 943705035
          rcases Nat.lt_or_ge n 943525179 with hs4 | hs4
          · -- n < 943525179
            rcases Nat.lt_or_ge n 943345323 with hs5 | hs5
            · -- n < 943345323
              exact Brocard.berndt_galway_chunk_5245 n m (by omega) (by omega) h
            · -- n >= 943345323
              exact Brocard.berndt_galway_chunk_5246 n m (by omega) (by omega) h
          · -- n >= 943525179
            exact Brocard.berndt_galway_chunk_5247 n m (by omega) (by omega) h
        · -- n >= 943705035
          rcases Nat.lt_or_ge n 944064748 with hs4 | hs4
          · -- n < 944064748
            rcases Nat.lt_or_ge n 943884892 with hs5 | hs5
            · -- n < 943884892
              exact Brocard.berndt_galway_chunk_5248 n m (by omega) (by omega) h
            · -- n >= 943884892
              exact Brocard.berndt_galway_chunk_5249 n m (by omega) (by omega) h
          · -- n >= 944064748
            exact Brocard.berndt_galway_chunk_5250 n m (by omega) (by omega) h
    · -- n >= 944244604
      rcases Nat.lt_or_ge n 945323741 with hs2 | hs2
      · -- n < 945323741
        rcases Nat.lt_or_ge n 944784172 with hs3 | hs3
        · -- n < 944784172
          rcases Nat.lt_or_ge n 944604316 with hs4 | hs4
          · -- n < 944604316
            rcases Nat.lt_or_ge n 944424460 with hs5 | hs5
            · -- n < 944424460
              exact Brocard.berndt_galway_chunk_5251 n m (by omega) (by omega) h
            · -- n >= 944424460
              exact Brocard.berndt_galway_chunk_5252 n m (by omega) (by omega) h
          · -- n >= 944604316
            exact Brocard.berndt_galway_chunk_5253 n m (by omega) (by omega) h
        · -- n >= 944784172
          rcases Nat.lt_or_ge n 945143884 with hs4 | hs4
          · -- n < 945143884
            rcases Nat.lt_or_ge n 944964028 with hs5 | hs5
            · -- n < 944964028
              exact Brocard.berndt_galway_chunk_5254 n m (by omega) (by omega) h
            · -- n >= 944964028
              exact Brocard.berndt_galway_chunk_5255 n m (by omega) (by omega) h
          · -- n >= 945143884
            exact Brocard.berndt_galway_chunk_5256 n m (by omega) (by omega) h
      · -- n >= 945323741
        rcases Nat.lt_or_ge n 945863309 with hs3 | hs3
        · -- n < 945863309
          rcases Nat.lt_or_ge n 945683453 with hs4 | hs4
          · -- n < 945683453
            rcases Nat.lt_or_ge n 945503597 with hs5 | hs5
            · -- n < 945503597
              exact Brocard.berndt_galway_chunk_5257 n m (by omega) (by omega) h
            · -- n >= 945503597
              exact Brocard.berndt_galway_chunk_5258 n m (by omega) (by omega) h
          · -- n >= 945683453
            exact Brocard.berndt_galway_chunk_5259 n m (by omega) (by omega) h
        · -- n >= 945863309
          rcases Nat.lt_or_ge n 946043165 with hs4 | hs4
          · -- n < 946043165
            exact Brocard.berndt_galway_chunk_5260 n m (by omega) (by omega) h
          · -- n >= 946043165
            exact Brocard.berndt_galway_chunk_5261 n m (by omega) (by omega) h
  · -- n >= 946223021
    rcases Nat.lt_or_ge n 948381294 with hs1 | hs1
    · -- n < 948381294
      rcases Nat.lt_or_ge n 947302158 with hs2 | hs2
      · -- n < 947302158
        rcases Nat.lt_or_ge n 946762589 with hs3 | hs3
        · -- n < 946762589
          rcases Nat.lt_or_ge n 946582733 with hs4 | hs4
          · -- n < 946582733
            rcases Nat.lt_or_ge n 946402877 with hs5 | hs5
            · -- n < 946402877
              exact Brocard.berndt_galway_chunk_5262 n m (by omega) (by omega) h
            · -- n >= 946402877
              exact Brocard.berndt_galway_chunk_5263 n m (by omega) (by omega) h
          · -- n >= 946582733
            exact Brocard.berndt_galway_chunk_5264 n m (by omega) (by omega) h
        · -- n >= 946762589
          rcases Nat.lt_or_ge n 947122302 with hs4 | hs4
          · -- n < 947122302
            rcases Nat.lt_or_ge n 946942446 with hs5 | hs5
            · -- n < 946942446
              exact Brocard.berndt_galway_chunk_5265 n m (by omega) (by omega) h
            · -- n >= 946942446
              exact Brocard.berndt_galway_chunk_5266 n m (by omega) (by omega) h
          · -- n >= 947122302
            exact Brocard.berndt_galway_chunk_5267 n m (by omega) (by omega) h
      · -- n >= 947302158
        rcases Nat.lt_or_ge n 947841726 with hs3 | hs3
        · -- n < 947841726
          rcases Nat.lt_or_ge n 947661870 with hs4 | hs4
          · -- n < 947661870
            rcases Nat.lt_or_ge n 947482014 with hs5 | hs5
            · -- n < 947482014
              exact Brocard.berndt_galway_chunk_5268 n m (by omega) (by omega) h
            · -- n >= 947482014
              exact Brocard.berndt_galway_chunk_5269 n m (by omega) (by omega) h
          · -- n >= 947661870
            exact Brocard.berndt_galway_chunk_5270 n m (by omega) (by omega) h
        · -- n >= 947841726
          rcases Nat.lt_or_ge n 948201438 with hs4 | hs4
          · -- n < 948201438
            rcases Nat.lt_or_ge n 948021582 with hs5 | hs5
            · -- n < 948021582
              exact Brocard.berndt_galway_chunk_5271 n m (by omega) (by omega) h
            · -- n >= 948021582
              exact Brocard.berndt_galway_chunk_5272 n m (by omega) (by omega) h
          · -- n >= 948201438
            exact Brocard.berndt_galway_chunk_5273 n m (by omega) (by omega) h
    · -- n >= 948381294
      rcases Nat.lt_or_ge n 949460431 with hs2 | hs2
      · -- n < 949460431
        rcases Nat.lt_or_ge n 948920863 with hs3 | hs3
        · -- n < 948920863
          rcases Nat.lt_or_ge n 948741007 with hs4 | hs4
          · -- n < 948741007
            rcases Nat.lt_or_ge n 948561151 with hs5 | hs5
            · -- n < 948561151
              exact Brocard.berndt_galway_chunk_5274 n m (by omega) (by omega) h
            · -- n >= 948561151
              exact Brocard.berndt_galway_chunk_5275 n m (by omega) (by omega) h
          · -- n >= 948741007
            exact Brocard.berndt_galway_chunk_5276 n m (by omega) (by omega) h
        · -- n >= 948920863
          rcases Nat.lt_or_ge n 949280575 with hs4 | hs4
          · -- n < 949280575
            rcases Nat.lt_or_ge n 949100719 with hs5 | hs5
            · -- n < 949100719
              exact Brocard.berndt_galway_chunk_5277 n m (by omega) (by omega) h
            · -- n >= 949100719
              exact Brocard.berndt_galway_chunk_5278 n m (by omega) (by omega) h
          · -- n >= 949280575
            exact Brocard.berndt_galway_chunk_5279 n m (by omega) (by omega) h
      · -- n >= 949460431
        rcases Nat.lt_or_ge n 950000000 with hs3 | hs3
        · -- n < 950000000
          rcases Nat.lt_or_ge n 949820143 with hs4 | hs4
          · -- n < 949820143
            rcases Nat.lt_or_ge n 949640287 with hs5 | hs5
            · -- n < 949640287
              exact Brocard.berndt_galway_chunk_5280 n m (by omega) (by omega) h
            · -- n >= 949640287
              exact Brocard.berndt_galway_chunk_5281 n m (by omega) (by omega) h
          · -- n >= 949820143
            exact Brocard.berndt_galway_chunk_5282 n m (by omega) (by omega) h
        · -- n >= 950000000
          rcases Nat.lt_or_ge n 950179856 with hs4 | hs4
          · -- n < 950179856
            exact Brocard.berndt_galway_chunk_5283 n m (by omega) (by omega) h
          · -- n >= 950179856
            exact Brocard.berndt_galway_chunk_5284 n m (by omega) (by omega) h
