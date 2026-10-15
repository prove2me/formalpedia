-- Prove2me | solution 1 for Brocard.berndt_galway_group_113
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:22:07.614538+00:00
-- url     : https://prove2.me/submissions/ccff2b39-5cc7-452c-9a8a-30d2c4d26d39

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_5193
import Theorems.Thm_Brocard_berndt_galway_chunk_5194
import Theorems.Thm_Brocard_berndt_galway_chunk_5195
import Theorems.Thm_Brocard_berndt_galway_chunk_5196
import Theorems.Thm_Brocard_berndt_galway_chunk_5197
import Theorems.Thm_Brocard_berndt_galway_chunk_5198
import Theorems.Thm_Brocard_berndt_galway_chunk_5199
import Theorems.Thm_Brocard_berndt_galway_chunk_5200
import Theorems.Thm_Brocard_berndt_galway_chunk_5201
import Theorems.Thm_Brocard_berndt_galway_chunk_5202
import Theorems.Thm_Brocard_berndt_galway_chunk_5203
import Theorems.Thm_Brocard_berndt_galway_chunk_5204
import Theorems.Thm_Brocard_berndt_galway_chunk_5205
import Theorems.Thm_Brocard_berndt_galway_chunk_5206
import Theorems.Thm_Brocard_berndt_galway_chunk_5207
import Theorems.Thm_Brocard_berndt_galway_chunk_5208
import Theorems.Thm_Brocard_berndt_galway_chunk_5209
import Theorems.Thm_Brocard_berndt_galway_chunk_5210
import Theorems.Thm_Brocard_berndt_galway_chunk_5211
import Theorems.Thm_Brocard_berndt_galway_chunk_5212
import Theorems.Thm_Brocard_berndt_galway_chunk_5213
import Theorems.Thm_Brocard_berndt_galway_chunk_5214
import Theorems.Thm_Brocard_berndt_galway_chunk_5215
import Theorems.Thm_Brocard_berndt_galway_chunk_5216
import Theorems.Thm_Brocard_berndt_galway_chunk_5217
import Theorems.Thm_Brocard_berndt_galway_chunk_5218
import Theorems.Thm_Brocard_berndt_galway_chunk_5219
import Theorems.Thm_Brocard_berndt_galway_chunk_5220
import Theorems.Thm_Brocard_berndt_galway_chunk_5221
import Theorems.Thm_Brocard_berndt_galway_chunk_5222
import Theorems.Thm_Brocard_berndt_galway_chunk_5223
import Theorems.Thm_Brocard_berndt_galway_chunk_5224
import Theorems.Thm_Brocard_berndt_galway_chunk_5225
import Theorems.Thm_Brocard_berndt_galway_chunk_5226
import Theorems.Thm_Brocard_berndt_galway_chunk_5227
import Theorems.Thm_Brocard_berndt_galway_chunk_5228
import Theorems.Thm_Brocard_berndt_galway_chunk_5229
import Theorems.Thm_Brocard_berndt_galway_chunk_5230
import Theorems.Thm_Brocard_berndt_galway_chunk_5231
import Theorems.Thm_Brocard_berndt_galway_chunk_5232
import Theorems.Thm_Brocard_berndt_galway_chunk_5233
import Theorems.Thm_Brocard_berndt_galway_chunk_5234
import Theorems.Thm_Brocard_berndt_galway_chunk_5235
import Theorems.Thm_Brocard_berndt_galway_chunk_5236
import Theorems.Thm_Brocard_berndt_galway_chunk_5237
import Theorems.Thm_Brocard_berndt_galway_chunk_5238

theorem solution (n m : ℕ) (h1 : 933812949 ≤ n) (h2 : n < 942086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 937949640 with hs0 | hs0
  · -- n < 937949640
    rcases Nat.lt_or_ge n 935971223 with hs1 | hs1
    · -- n < 935971223
      rcases Nat.lt_or_ge n 934892086 with hs2 | hs2
      · -- n < 934892086
        rcases Nat.lt_or_ge n 934352517 with hs3 | hs3
        · -- n < 934352517
          rcases Nat.lt_or_ge n 934172661 with hs4 | hs4
          · -- n < 934172661
            rcases Nat.lt_or_ge n 933992805 with hs5 | hs5
            · -- n < 933992805
              exact Brocard.berndt_galway_chunk_5193 n m (by omega) (by omega) h
            · -- n >= 933992805
              exact Brocard.berndt_galway_chunk_5194 n m (by omega) (by omega) h
          · -- n >= 934172661
            exact Brocard.berndt_galway_chunk_5195 n m (by omega) (by omega) h
        · -- n >= 934352517
          rcases Nat.lt_or_ge n 934712230 with hs4 | hs4
          · -- n < 934712230
            rcases Nat.lt_or_ge n 934532374 with hs5 | hs5
            · -- n < 934532374
              exact Brocard.berndt_galway_chunk_5196 n m (by omega) (by omega) h
            · -- n >= 934532374
              exact Brocard.berndt_galway_chunk_5197 n m (by omega) (by omega) h
          · -- n >= 934712230
            exact Brocard.berndt_galway_chunk_5198 n m (by omega) (by omega) h
      · -- n >= 934892086
        rcases Nat.lt_or_ge n 935431654 with hs3 | hs3
        · -- n < 935431654
          rcases Nat.lt_or_ge n 935251798 with hs4 | hs4
          · -- n < 935251798
            rcases Nat.lt_or_ge n 935071942 with hs5 | hs5
            · -- n < 935071942
              exact Brocard.berndt_galway_chunk_5199 n m (by omega) (by omega) h
            · -- n >= 935071942
              exact Brocard.berndt_galway_chunk_5200 n m (by omega) (by omega) h
          · -- n >= 935251798
            exact Brocard.berndt_galway_chunk_5201 n m (by omega) (by omega) h
        · -- n >= 935431654
          rcases Nat.lt_or_ge n 935791366 with hs4 | hs4
          · -- n < 935791366
            rcases Nat.lt_or_ge n 935611510 with hs5 | hs5
            · -- n < 935611510
              exact Brocard.berndt_galway_chunk_5202 n m (by omega) (by omega) h
            · -- n >= 935611510
              exact Brocard.berndt_galway_chunk_5203 n m (by omega) (by omega) h
          · -- n >= 935791366
            exact Brocard.berndt_galway_chunk_5204 n m (by omega) (by omega) h
    · -- n >= 935971223
      rcases Nat.lt_or_ge n 937050359 with hs2 | hs2
      · -- n < 937050359
        rcases Nat.lt_or_ge n 936510791 with hs3 | hs3
        · -- n < 936510791
          rcases Nat.lt_or_ge n 936330935 with hs4 | hs4
          · -- n < 936330935
            rcases Nat.lt_or_ge n 936151079 with hs5 | hs5
            · -- n < 936151079
              exact Brocard.berndt_galway_chunk_5205 n m (by omega) (by omega) h
            · -- n >= 936151079
              exact Brocard.berndt_galway_chunk_5206 n m (by omega) (by omega) h
          · -- n >= 936330935
            exact Brocard.berndt_galway_chunk_5207 n m (by omega) (by omega) h
        · -- n >= 936510791
          rcases Nat.lt_or_ge n 936870503 with hs4 | hs4
          · -- n < 936870503
            rcases Nat.lt_or_ge n 936690647 with hs5 | hs5
            · -- n < 936690647
              exact Brocard.berndt_galway_chunk_5208 n m (by omega) (by omega) h
            · -- n >= 936690647
              exact Brocard.berndt_galway_chunk_5209 n m (by omega) (by omega) h
          · -- n >= 936870503
            exact Brocard.berndt_galway_chunk_5210 n m (by omega) (by omega) h
      · -- n >= 937050359
        rcases Nat.lt_or_ge n 937589928 with hs3 | hs3
        · -- n < 937589928
          rcases Nat.lt_or_ge n 937410071 with hs4 | hs4
          · -- n < 937410071
            rcases Nat.lt_or_ge n 937230215 with hs5 | hs5
            · -- n < 937230215
              exact Brocard.berndt_galway_chunk_5211 n m (by omega) (by omega) h
            · -- n >= 937230215
              exact Brocard.berndt_galway_chunk_5212 n m (by omega) (by omega) h
          · -- n >= 937410071
            exact Brocard.berndt_galway_chunk_5213 n m (by omega) (by omega) h
        · -- n >= 937589928
          rcases Nat.lt_or_ge n 937769784 with hs4 | hs4
          · -- n < 937769784
            exact Brocard.berndt_galway_chunk_5214 n m (by omega) (by omega) h
          · -- n >= 937769784
            exact Brocard.berndt_galway_chunk_5215 n m (by omega) (by omega) h
  · -- n >= 937949640
    rcases Nat.lt_or_ge n 940107913 with hs1 | hs1
    · -- n < 940107913
      rcases Nat.lt_or_ge n 939028776 with hs2 | hs2
      · -- n < 939028776
        rcases Nat.lt_or_ge n 938489208 with hs3 | hs3
        · -- n < 938489208
          rcases Nat.lt_or_ge n 938309352 with hs4 | hs4
          · -- n < 938309352
            rcases Nat.lt_or_ge n 938129496 with hs5 | hs5
            · -- n < 938129496
              exact Brocard.berndt_galway_chunk_5216 n m (by omega) (by omega) h
            · -- n >= 938129496
              exact Brocard.berndt_galway_chunk_5217 n m (by omega) (by omega) h
          · -- n >= 938309352
            exact Brocard.berndt_galway_chunk_5218 n m (by omega) (by omega) h
        · -- n >= 938489208
          rcases Nat.lt_or_ge n 938848920 with hs4 | hs4
          · -- n < 938848920
            rcases Nat.lt_or_ge n 938669064 with hs5 | hs5
            · -- n < 938669064
              exact Brocard.berndt_galway_chunk_5219 n m (by omega) (by omega) h
            · -- n >= 938669064
              exact Brocard.berndt_galway_chunk_5220 n m (by omega) (by omega) h
          · -- n >= 938848920
            exact Brocard.berndt_galway_chunk_5221 n m (by omega) (by omega) h
      · -- n >= 939028776
        rcases Nat.lt_or_ge n 939568345 with hs3 | hs3
        · -- n < 939568345
          rcases Nat.lt_or_ge n 939388489 with hs4 | hs4
          · -- n < 939388489
            rcases Nat.lt_or_ge n 939208633 with hs5 | hs5
            · -- n < 939208633
              exact Brocard.berndt_galway_chunk_5222 n m (by omega) (by omega) h
            · -- n >= 939208633
              exact Brocard.berndt_galway_chunk_5223 n m (by omega) (by omega) h
          · -- n >= 939388489
            exact Brocard.berndt_galway_chunk_5224 n m (by omega) (by omega) h
        · -- n >= 939568345
          rcases Nat.lt_or_ge n 939928057 with hs4 | hs4
          · -- n < 939928057
            rcases Nat.lt_or_ge n 939748201 with hs5 | hs5
            · -- n < 939748201
              exact Brocard.berndt_galway_chunk_5225 n m (by omega) (by omega) h
            · -- n >= 939748201
              exact Brocard.berndt_galway_chunk_5226 n m (by omega) (by omega) h
          · -- n >= 939928057
            exact Brocard.berndt_galway_chunk_5227 n m (by omega) (by omega) h
    · -- n >= 940107913
      rcases Nat.lt_or_ge n 941187050 with hs2 | hs2
      · -- n < 941187050
        rcases Nat.lt_or_ge n 940647482 with hs3 | hs3
        · -- n < 940647482
          rcases Nat.lt_or_ge n 940467625 with hs4 | hs4
          · -- n < 940467625
            rcases Nat.lt_or_ge n 940287769 with hs5 | hs5
            · -- n < 940287769
              exact Brocard.berndt_galway_chunk_5228 n m (by omega) (by omega) h
            · -- n >= 940287769
              exact Brocard.berndt_galway_chunk_5229 n m (by omega) (by omega) h
          · -- n >= 940467625
            exact Brocard.berndt_galway_chunk_5230 n m (by omega) (by omega) h
        · -- n >= 940647482
          rcases Nat.lt_or_ge n 941007194 with hs4 | hs4
          · -- n < 941007194
            rcases Nat.lt_or_ge n 940827338 with hs5 | hs5
            · -- n < 940827338
              exact Brocard.berndt_galway_chunk_5231 n m (by omega) (by omega) h
            · -- n >= 940827338
              exact Brocard.berndt_galway_chunk_5232 n m (by omega) (by omega) h
          · -- n >= 941007194
            exact Brocard.berndt_galway_chunk_5233 n m (by omega) (by omega) h
      · -- n >= 941187050
        rcases Nat.lt_or_ge n 941726618 with hs3 | hs3
        · -- n < 941726618
          rcases Nat.lt_or_ge n 941546762 with hs4 | hs4
          · -- n < 941546762
            rcases Nat.lt_or_ge n 941366906 with hs5 | hs5
            · -- n < 941366906
              exact Brocard.berndt_galway_chunk_5234 n m (by omega) (by omega) h
            · -- n >= 941366906
              exact Brocard.berndt_galway_chunk_5235 n m (by omega) (by omega) h
          · -- n >= 941546762
            exact Brocard.berndt_galway_chunk_5236 n m (by omega) (by omega) h
        · -- n >= 941726618
          rcases Nat.lt_or_ge n 941906474 with hs4 | hs4
          · -- n < 941906474
            exact Brocard.berndt_galway_chunk_5237 n m (by omega) (by omega) h
          · -- n >= 941906474
            exact Brocard.berndt_galway_chunk_5238 n m (by omega) (by omega) h
