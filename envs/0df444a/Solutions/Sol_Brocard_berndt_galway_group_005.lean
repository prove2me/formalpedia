-- Prove2me | solution 1 for Brocard.berndt_galway_group_005
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:47:10.178982+00:00
-- url     : https://prove2.me/submissions/c350320f-d72b-4c69-bda0-d621c530bbf5

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_0189
import Theorems.Thm_Brocard_berndt_galway_chunk_0190
import Theorems.Thm_Brocard_berndt_galway_chunk_0191
import Theorems.Thm_Brocard_berndt_galway_chunk_0192
import Theorems.Thm_Brocard_berndt_galway_chunk_0193
import Theorems.Thm_Brocard_berndt_galway_chunk_0194
import Theorems.Thm_Brocard_berndt_galway_chunk_0195
import Theorems.Thm_Brocard_berndt_galway_chunk_0196
import Theorems.Thm_Brocard_berndt_galway_chunk_0197
import Theorems.Thm_Brocard_berndt_galway_chunk_0198
import Theorems.Thm_Brocard_berndt_galway_chunk_0199
import Theorems.Thm_Brocard_berndt_galway_chunk_0200
import Theorems.Thm_Brocard_berndt_galway_chunk_0201
import Theorems.Thm_Brocard_berndt_galway_chunk_0202
import Theorems.Thm_Brocard_berndt_galway_chunk_0203
import Theorems.Thm_Brocard_berndt_galway_chunk_0204
import Theorems.Thm_Brocard_berndt_galway_chunk_0205
import Theorems.Thm_Brocard_berndt_galway_chunk_0206
import Theorems.Thm_Brocard_berndt_galway_chunk_0207
import Theorems.Thm_Brocard_berndt_galway_chunk_0208
import Theorems.Thm_Brocard_berndt_galway_chunk_0209
import Theorems.Thm_Brocard_berndt_galway_chunk_0210
import Theorems.Thm_Brocard_berndt_galway_chunk_0211
import Theorems.Thm_Brocard_berndt_galway_chunk_0212
import Theorems.Thm_Brocard_berndt_galway_chunk_0213
import Theorems.Thm_Brocard_berndt_galway_chunk_0214
import Theorems.Thm_Brocard_berndt_galway_chunk_0215
import Theorems.Thm_Brocard_berndt_galway_chunk_0216
import Theorems.Thm_Brocard_berndt_galway_chunk_0217
import Theorems.Thm_Brocard_berndt_galway_chunk_0218
import Theorems.Thm_Brocard_berndt_galway_chunk_0219
import Theorems.Thm_Brocard_berndt_galway_chunk_0220
import Theorems.Thm_Brocard_berndt_galway_chunk_0221
import Theorems.Thm_Brocard_berndt_galway_chunk_0222
import Theorems.Thm_Brocard_berndt_galway_chunk_0223
import Theorems.Thm_Brocard_berndt_galway_chunk_0224
import Theorems.Thm_Brocard_berndt_galway_chunk_0225
import Theorems.Thm_Brocard_berndt_galway_chunk_0226
import Theorems.Thm_Brocard_berndt_galway_chunk_0227
import Theorems.Thm_Brocard_berndt_galway_chunk_0228
import Theorems.Thm_Brocard_berndt_galway_chunk_0229
import Theorems.Thm_Brocard_berndt_galway_chunk_0230
import Theorems.Thm_Brocard_berndt_galway_chunk_0231
import Theorems.Thm_Brocard_berndt_galway_chunk_0232
import Theorems.Thm_Brocard_berndt_galway_chunk_0233
import Theorems.Thm_Brocard_berndt_galway_chunk_0234

theorem solution (n m : ℕ) (h1 : 33812954 ≤ n) (h2 : n < 42086335) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 37949645 with hs0 | hs0
  · -- n < 37949645
    rcases Nat.lt_or_ge n 35971228 with hs1 | hs1
    · -- n < 35971228
      rcases Nat.lt_or_ge n 34892091 with hs2 | hs2
      · -- n < 34892091
        rcases Nat.lt_or_ge n 34352523 with hs3 | hs3
        · -- n < 34352523
          rcases Nat.lt_or_ge n 34172667 with hs4 | hs4
          · -- n < 34172667
            rcases Nat.lt_or_ge n 33992811 with hs5 | hs5
            · -- n < 33992811
              exact Brocard.berndt_galway_chunk_0189 n m (by omega) (by omega) h
            · -- n >= 33992811
              exact Brocard.berndt_galway_chunk_0190 n m (by omega) (by omega) h
          · -- n >= 34172667
            exact Brocard.berndt_galway_chunk_0191 n m (by omega) (by omega) h
        · -- n >= 34352523
          rcases Nat.lt_or_ge n 34712235 with hs4 | hs4
          · -- n < 34712235
            rcases Nat.lt_or_ge n 34532379 with hs5 | hs5
            · -- n < 34532379
              exact Brocard.berndt_galway_chunk_0192 n m (by omega) (by omega) h
            · -- n >= 34532379
              exact Brocard.berndt_galway_chunk_0193 n m (by omega) (by omega) h
          · -- n >= 34712235
            exact Brocard.berndt_galway_chunk_0194 n m (by omega) (by omega) h
      · -- n >= 34892091
        rcases Nat.lt_or_ge n 35431659 with hs3 | hs3
        · -- n < 35431659
          rcases Nat.lt_or_ge n 35251803 with hs4 | hs4
          · -- n < 35251803
            rcases Nat.lt_or_ge n 35071947 with hs5 | hs5
            · -- n < 35071947
              exact Brocard.berndt_galway_chunk_0195 n m (by omega) (by omega) h
            · -- n >= 35071947
              exact Brocard.berndt_galway_chunk_0196 n m (by omega) (by omega) h
          · -- n >= 35251803
            exact Brocard.berndt_galway_chunk_0197 n m (by omega) (by omega) h
        · -- n >= 35431659
          rcases Nat.lt_or_ge n 35791372 with hs4 | hs4
          · -- n < 35791372
            rcases Nat.lt_or_ge n 35611515 with hs5 | hs5
            · -- n < 35611515
              exact Brocard.berndt_galway_chunk_0198 n m (by omega) (by omega) h
            · -- n >= 35611515
              exact Brocard.berndt_galway_chunk_0199 n m (by omega) (by omega) h
          · -- n >= 35791372
            exact Brocard.berndt_galway_chunk_0200 n m (by omega) (by omega) h
    · -- n >= 35971228
      rcases Nat.lt_or_ge n 37050364 with hs2 | hs2
      · -- n < 37050364
        rcases Nat.lt_or_ge n 36510796 with hs3 | hs3
        · -- n < 36510796
          rcases Nat.lt_or_ge n 36330940 with hs4 | hs4
          · -- n < 36330940
            rcases Nat.lt_or_ge n 36151084 with hs5 | hs5
            · -- n < 36151084
              exact Brocard.berndt_galway_chunk_0201 n m (by omega) (by omega) h
            · -- n >= 36151084
              exact Brocard.berndt_galway_chunk_0202 n m (by omega) (by omega) h
          · -- n >= 36330940
            exact Brocard.berndt_galway_chunk_0203 n m (by omega) (by omega) h
        · -- n >= 36510796
          rcases Nat.lt_or_ge n 36870508 with hs4 | hs4
          · -- n < 36870508
            rcases Nat.lt_or_ge n 36690652 with hs5 | hs5
            · -- n < 36690652
              exact Brocard.berndt_galway_chunk_0204 n m (by omega) (by omega) h
            · -- n >= 36690652
              exact Brocard.berndt_galway_chunk_0205 n m (by omega) (by omega) h
          · -- n >= 36870508
            exact Brocard.berndt_galway_chunk_0206 n m (by omega) (by omega) h
      · -- n >= 37050364
        rcases Nat.lt_or_ge n 37589933 with hs3 | hs3
        · -- n < 37589933
          rcases Nat.lt_or_ge n 37410076 with hs4 | hs4
          · -- n < 37410076
            rcases Nat.lt_or_ge n 37230220 with hs5 | hs5
            · -- n < 37230220
              exact Brocard.berndt_galway_chunk_0207 n m (by omega) (by omega) h
            · -- n >= 37230220
              exact Brocard.berndt_galway_chunk_0208 n m (by omega) (by omega) h
          · -- n >= 37410076
            exact Brocard.berndt_galway_chunk_0209 n m (by omega) (by omega) h
        · -- n >= 37589933
          rcases Nat.lt_or_ge n 37769789 with hs4 | hs4
          · -- n < 37769789
            exact Brocard.berndt_galway_chunk_0210 n m (by omega) (by omega) h
          · -- n >= 37769789
            exact Brocard.berndt_galway_chunk_0211 n m (by omega) (by omega) h
  · -- n >= 37949645
    rcases Nat.lt_or_ge n 40107918 with hs1 | hs1
    · -- n < 40107918
      rcases Nat.lt_or_ge n 39028781 with hs2 | hs2
      · -- n < 39028781
        rcases Nat.lt_or_ge n 38489213 with hs3 | hs3
        · -- n < 38489213
          rcases Nat.lt_or_ge n 38309357 with hs4 | hs4
          · -- n < 38309357
            rcases Nat.lt_or_ge n 38129501 with hs5 | hs5
            · -- n < 38129501
              exact Brocard.berndt_galway_chunk_0212 n m (by omega) (by omega) h
            · -- n >= 38129501
              exact Brocard.berndt_galway_chunk_0213 n m (by omega) (by omega) h
          · -- n >= 38309357
            exact Brocard.berndt_galway_chunk_0214 n m (by omega) (by omega) h
        · -- n >= 38489213
          rcases Nat.lt_or_ge n 38848925 with hs4 | hs4
          · -- n < 38848925
            rcases Nat.lt_or_ge n 38669069 with hs5 | hs5
            · -- n < 38669069
              exact Brocard.berndt_galway_chunk_0215 n m (by omega) (by omega) h
            · -- n >= 38669069
              exact Brocard.berndt_galway_chunk_0216 n m (by omega) (by omega) h
          · -- n >= 38848925
            exact Brocard.berndt_galway_chunk_0217 n m (by omega) (by omega) h
      · -- n >= 39028781
        rcases Nat.lt_or_ge n 39568350 with hs3 | hs3
        · -- n < 39568350
          rcases Nat.lt_or_ge n 39388494 with hs4 | hs4
          · -- n < 39388494
            rcases Nat.lt_or_ge n 39208637 with hs5 | hs5
            · -- n < 39208637
              exact Brocard.berndt_galway_chunk_0218 n m (by omega) (by omega) h
            · -- n >= 39208637
              exact Brocard.berndt_galway_chunk_0219 n m (by omega) (by omega) h
          · -- n >= 39388494
            exact Brocard.berndt_galway_chunk_0220 n m (by omega) (by omega) h
        · -- n >= 39568350
          rcases Nat.lt_or_ge n 39928062 with hs4 | hs4
          · -- n < 39928062
            rcases Nat.lt_or_ge n 39748206 with hs5 | hs5
            · -- n < 39748206
              exact Brocard.berndt_galway_chunk_0221 n m (by omega) (by omega) h
            · -- n >= 39748206
              exact Brocard.berndt_galway_chunk_0222 n m (by omega) (by omega) h
          · -- n >= 39928062
            exact Brocard.berndt_galway_chunk_0223 n m (by omega) (by omega) h
    · -- n >= 40107918
      rcases Nat.lt_or_ge n 41187055 with hs2 | hs2
      · -- n < 41187055
        rcases Nat.lt_or_ge n 40647486 with hs3 | hs3
        · -- n < 40647486
          rcases Nat.lt_or_ge n 40467630 with hs4 | hs4
          · -- n < 40467630
            rcases Nat.lt_or_ge n 40287774 with hs5 | hs5
            · -- n < 40287774
              exact Brocard.berndt_galway_chunk_0224 n m (by omega) (by omega) h
            · -- n >= 40287774
              exact Brocard.berndt_galway_chunk_0225 n m (by omega) (by omega) h
          · -- n >= 40467630
            exact Brocard.berndt_galway_chunk_0226 n m (by omega) (by omega) h
        · -- n >= 40647486
          rcases Nat.lt_or_ge n 41007198 with hs4 | hs4
          · -- n < 41007198
            rcases Nat.lt_or_ge n 40827342 with hs5 | hs5
            · -- n < 40827342
              exact Brocard.berndt_galway_chunk_0227 n m (by omega) (by omega) h
            · -- n >= 40827342
              exact Brocard.berndt_galway_chunk_0228 n m (by omega) (by omega) h
          · -- n >= 41007198
            exact Brocard.berndt_galway_chunk_0229 n m (by omega) (by omega) h
      · -- n >= 41187055
        rcases Nat.lt_or_ge n 41726623 with hs3 | hs3
        · -- n < 41726623
          rcases Nat.lt_or_ge n 41546767 with hs4 | hs4
          · -- n < 41546767
            rcases Nat.lt_or_ge n 41366911 with hs5 | hs5
            · -- n < 41366911
              exact Brocard.berndt_galway_chunk_0230 n m (by omega) (by omega) h
            · -- n >= 41366911
              exact Brocard.berndt_galway_chunk_0231 n m (by omega) (by omega) h
          · -- n >= 41546767
            exact Brocard.berndt_galway_chunk_0232 n m (by omega) (by omega) h
        · -- n >= 41726623
          rcases Nat.lt_or_ge n 41906479 with hs4 | hs4
          · -- n < 41906479
            exact Brocard.berndt_galway_chunk_0233 n m (by omega) (by omega) h
          · -- n >= 41906479
            exact Brocard.berndt_galway_chunk_0234 n m (by omega) (by omega) h
