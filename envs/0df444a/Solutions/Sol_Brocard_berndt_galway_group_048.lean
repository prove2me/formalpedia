-- Prove2me | solution 1 for Brocard.berndt_galway_group_048
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:11:58.040783+00:00
-- url     : https://prove2.me/submissions/19f077b1-389d-4140-93b9-5c7e117bb8fa

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_2179
import Theorems.Thm_Brocard_berndt_galway_chunk_2180
import Theorems.Thm_Brocard_berndt_galway_chunk_2181
import Theorems.Thm_Brocard_berndt_galway_chunk_2182
import Theorems.Thm_Brocard_berndt_galway_chunk_2183
import Theorems.Thm_Brocard_berndt_galway_chunk_2184
import Theorems.Thm_Brocard_berndt_galway_chunk_2185
import Theorems.Thm_Brocard_berndt_galway_chunk_2186
import Theorems.Thm_Brocard_berndt_galway_chunk_2187
import Theorems.Thm_Brocard_berndt_galway_chunk_2188
import Theorems.Thm_Brocard_berndt_galway_chunk_2189
import Theorems.Thm_Brocard_berndt_galway_chunk_2190
import Theorems.Thm_Brocard_berndt_galway_chunk_2191
import Theorems.Thm_Brocard_berndt_galway_chunk_2192
import Theorems.Thm_Brocard_berndt_galway_chunk_2193
import Theorems.Thm_Brocard_berndt_galway_chunk_2194
import Theorems.Thm_Brocard_berndt_galway_chunk_2195
import Theorems.Thm_Brocard_berndt_galway_chunk_2196
import Theorems.Thm_Brocard_berndt_galway_chunk_2197
import Theorems.Thm_Brocard_berndt_galway_chunk_2198
import Theorems.Thm_Brocard_berndt_galway_chunk_2199
import Theorems.Thm_Brocard_berndt_galway_chunk_2200
import Theorems.Thm_Brocard_berndt_galway_chunk_2201
import Theorems.Thm_Brocard_berndt_galway_chunk_2202
import Theorems.Thm_Brocard_berndt_galway_chunk_2203
import Theorems.Thm_Brocard_berndt_galway_chunk_2204
import Theorems.Thm_Brocard_berndt_galway_chunk_2205
import Theorems.Thm_Brocard_berndt_galway_chunk_2206
import Theorems.Thm_Brocard_berndt_galway_chunk_2207
import Theorems.Thm_Brocard_berndt_galway_chunk_2208
import Theorems.Thm_Brocard_berndt_galway_chunk_2209
import Theorems.Thm_Brocard_berndt_galway_chunk_2210
import Theorems.Thm_Brocard_berndt_galway_chunk_2211
import Theorems.Thm_Brocard_berndt_galway_chunk_2212
import Theorems.Thm_Brocard_berndt_galway_chunk_2213
import Theorems.Thm_Brocard_berndt_galway_chunk_2214
import Theorems.Thm_Brocard_berndt_galway_chunk_2215
import Theorems.Thm_Brocard_berndt_galway_chunk_2216
import Theorems.Thm_Brocard_berndt_galway_chunk_2217
import Theorems.Thm_Brocard_berndt_galway_chunk_2218
import Theorems.Thm_Brocard_berndt_galway_chunk_2219
import Theorems.Thm_Brocard_berndt_galway_chunk_2220
import Theorems.Thm_Brocard_berndt_galway_chunk_2221
import Theorems.Thm_Brocard_berndt_galway_chunk_2222
import Theorems.Thm_Brocard_berndt_galway_chunk_2223
import Theorems.Thm_Brocard_berndt_galway_chunk_2224

theorem solution (n m : ℕ) (h1 : 391726618 ≤ n) (h2 : n < 400000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 395863309 with hs0 | hs0
  · -- n < 395863309
    rcases Nat.lt_or_ge n 393884892 with hs1 | hs1
    · -- n < 393884892
      rcases Nat.lt_or_ge n 392805755 with hs2 | hs2
      · -- n < 392805755
        rcases Nat.lt_or_ge n 392266187 with hs3 | hs3
        · -- n < 392266187
          rcases Nat.lt_or_ge n 392086330 with hs4 | hs4
          · -- n < 392086330
            rcases Nat.lt_or_ge n 391906474 with hs5 | hs5
            · -- n < 391906474
              exact Brocard.berndt_galway_chunk_2179 n m (by omega) (by omega) h
            · -- n >= 391906474
              exact Brocard.berndt_galway_chunk_2180 n m (by omega) (by omega) h
          · -- n >= 392086330
            exact Brocard.berndt_galway_chunk_2181 n m (by omega) (by omega) h
        · -- n >= 392266187
          rcases Nat.lt_or_ge n 392625899 with hs4 | hs4
          · -- n < 392625899
            rcases Nat.lt_or_ge n 392446043 with hs5 | hs5
            · -- n < 392446043
              exact Brocard.berndt_galway_chunk_2182 n m (by omega) (by omega) h
            · -- n >= 392446043
              exact Brocard.berndt_galway_chunk_2183 n m (by omega) (by omega) h
          · -- n >= 392625899
            exact Brocard.berndt_galway_chunk_2184 n m (by omega) (by omega) h
      · -- n >= 392805755
        rcases Nat.lt_or_ge n 393345323 with hs3 | hs3
        · -- n < 393345323
          rcases Nat.lt_or_ge n 393165467 with hs4 | hs4
          · -- n < 393165467
            rcases Nat.lt_or_ge n 392985611 with hs5 | hs5
            · -- n < 392985611
              exact Brocard.berndt_galway_chunk_2185 n m (by omega) (by omega) h
            · -- n >= 392985611
              exact Brocard.berndt_galway_chunk_2186 n m (by omega) (by omega) h
          · -- n >= 393165467
            exact Brocard.berndt_galway_chunk_2187 n m (by omega) (by omega) h
        · -- n >= 393345323
          rcases Nat.lt_or_ge n 393705035 with hs4 | hs4
          · -- n < 393705035
            rcases Nat.lt_or_ge n 393525179 with hs5 | hs5
            · -- n < 393525179
              exact Brocard.berndt_galway_chunk_2188 n m (by omega) (by omega) h
            · -- n >= 393525179
              exact Brocard.berndt_galway_chunk_2189 n m (by omega) (by omega) h
          · -- n >= 393705035
            exact Brocard.berndt_galway_chunk_2190 n m (by omega) (by omega) h
    · -- n >= 393884892
      rcases Nat.lt_or_ge n 394964028 with hs2 | hs2
      · -- n < 394964028
        rcases Nat.lt_or_ge n 394424460 with hs3 | hs3
        · -- n < 394424460
          rcases Nat.lt_or_ge n 394244604 with hs4 | hs4
          · -- n < 394244604
            rcases Nat.lt_or_ge n 394064748 with hs5 | hs5
            · -- n < 394064748
              exact Brocard.berndt_galway_chunk_2191 n m (by omega) (by omega) h
            · -- n >= 394064748
              exact Brocard.berndt_galway_chunk_2192 n m (by omega) (by omega) h
          · -- n >= 394244604
            exact Brocard.berndt_galway_chunk_2193 n m (by omega) (by omega) h
        · -- n >= 394424460
          rcases Nat.lt_or_ge n 394784172 with hs4 | hs4
          · -- n < 394784172
            rcases Nat.lt_or_ge n 394604316 with hs5 | hs5
            · -- n < 394604316
              exact Brocard.berndt_galway_chunk_2194 n m (by omega) (by omega) h
            · -- n >= 394604316
              exact Brocard.berndt_galway_chunk_2195 n m (by omega) (by omega) h
          · -- n >= 394784172
            exact Brocard.berndt_galway_chunk_2196 n m (by omega) (by omega) h
      · -- n >= 394964028
        rcases Nat.lt_or_ge n 395503597 with hs3 | hs3
        · -- n < 395503597
          rcases Nat.lt_or_ge n 395323741 with hs4 | hs4
          · -- n < 395323741
            rcases Nat.lt_or_ge n 395143884 with hs5 | hs5
            · -- n < 395143884
              exact Brocard.berndt_galway_chunk_2197 n m (by omega) (by omega) h
            · -- n >= 395143884
              exact Brocard.berndt_galway_chunk_2198 n m (by omega) (by omega) h
          · -- n >= 395323741
            exact Brocard.berndt_galway_chunk_2199 n m (by omega) (by omega) h
        · -- n >= 395503597
          rcases Nat.lt_or_ge n 395683453 with hs4 | hs4
          · -- n < 395683453
            exact Brocard.berndt_galway_chunk_2200 n m (by omega) (by omega) h
          · -- n >= 395683453
            exact Brocard.berndt_galway_chunk_2201 n m (by omega) (by omega) h
  · -- n >= 395863309
    rcases Nat.lt_or_ge n 398021582 with hs1 | hs1
    · -- n < 398021582
      rcases Nat.lt_or_ge n 396942446 with hs2 | hs2
      · -- n < 396942446
        rcases Nat.lt_or_ge n 396402877 with hs3 | hs3
        · -- n < 396402877
          rcases Nat.lt_or_ge n 396223021 with hs4 | hs4
          · -- n < 396223021
            rcases Nat.lt_or_ge n 396043165 with hs5 | hs5
            · -- n < 396043165
              exact Brocard.berndt_galway_chunk_2202 n m (by omega) (by omega) h
            · -- n >= 396043165
              exact Brocard.berndt_galway_chunk_2203 n m (by omega) (by omega) h
          · -- n >= 396223021
            exact Brocard.berndt_galway_chunk_2204 n m (by omega) (by omega) h
        · -- n >= 396402877
          rcases Nat.lt_or_ge n 396762589 with hs4 | hs4
          · -- n < 396762589
            rcases Nat.lt_or_ge n 396582733 with hs5 | hs5
            · -- n < 396582733
              exact Brocard.berndt_galway_chunk_2205 n m (by omega) (by omega) h
            · -- n >= 396582733
              exact Brocard.berndt_galway_chunk_2206 n m (by omega) (by omega) h
          · -- n >= 396762589
            exact Brocard.berndt_galway_chunk_2207 n m (by omega) (by omega) h
      · -- n >= 396942446
        rcases Nat.lt_or_ge n 397482014 with hs3 | hs3
        · -- n < 397482014
          rcases Nat.lt_or_ge n 397302158 with hs4 | hs4
          · -- n < 397302158
            rcases Nat.lt_or_ge n 397122302 with hs5 | hs5
            · -- n < 397122302
              exact Brocard.berndt_galway_chunk_2208 n m (by omega) (by omega) h
            · -- n >= 397122302
              exact Brocard.berndt_galway_chunk_2209 n m (by omega) (by omega) h
          · -- n >= 397302158
            exact Brocard.berndt_galway_chunk_2210 n m (by omega) (by omega) h
        · -- n >= 397482014
          rcases Nat.lt_or_ge n 397841726 with hs4 | hs4
          · -- n < 397841726
            rcases Nat.lt_or_ge n 397661870 with hs5 | hs5
            · -- n < 397661870
              exact Brocard.berndt_galway_chunk_2211 n m (by omega) (by omega) h
            · -- n >= 397661870
              exact Brocard.berndt_galway_chunk_2212 n m (by omega) (by omega) h
          · -- n >= 397841726
            exact Brocard.berndt_galway_chunk_2213 n m (by omega) (by omega) h
    · -- n >= 398021582
      rcases Nat.lt_or_ge n 399100719 with hs2 | hs2
      · -- n < 399100719
        rcases Nat.lt_or_ge n 398561151 with hs3 | hs3
        · -- n < 398561151
          rcases Nat.lt_or_ge n 398381294 with hs4 | hs4
          · -- n < 398381294
            rcases Nat.lt_or_ge n 398201438 with hs5 | hs5
            · -- n < 398201438
              exact Brocard.berndt_galway_chunk_2214 n m (by omega) (by omega) h
            · -- n >= 398201438
              exact Brocard.berndt_galway_chunk_2215 n m (by omega) (by omega) h
          · -- n >= 398381294
            exact Brocard.berndt_galway_chunk_2216 n m (by omega) (by omega) h
        · -- n >= 398561151
          rcases Nat.lt_or_ge n 398920863 with hs4 | hs4
          · -- n < 398920863
            rcases Nat.lt_or_ge n 398741007 with hs5 | hs5
            · -- n < 398741007
              exact Brocard.berndt_galway_chunk_2217 n m (by omega) (by omega) h
            · -- n >= 398741007
              exact Brocard.berndt_galway_chunk_2218 n m (by omega) (by omega) h
          · -- n >= 398920863
            exact Brocard.berndt_galway_chunk_2219 n m (by omega) (by omega) h
      · -- n >= 399100719
        rcases Nat.lt_or_ge n 399640287 with hs3 | hs3
        · -- n < 399640287
          rcases Nat.lt_or_ge n 399460431 with hs4 | hs4
          · -- n < 399460431
            rcases Nat.lt_or_ge n 399280575 with hs5 | hs5
            · -- n < 399280575
              exact Brocard.berndt_galway_chunk_2220 n m (by omega) (by omega) h
            · -- n >= 399280575
              exact Brocard.berndt_galway_chunk_2221 n m (by omega) (by omega) h
          · -- n >= 399460431
            exact Brocard.berndt_galway_chunk_2222 n m (by omega) (by omega) h
        · -- n >= 399640287
          rcases Nat.lt_or_ge n 399820143 with hs4 | hs4
          · -- n < 399820143
            exact Brocard.berndt_galway_chunk_2223 n m (by omega) (by omega) h
          · -- n >= 399820143
            exact Brocard.berndt_galway_chunk_2224 n m (by omega) (by omega) h
