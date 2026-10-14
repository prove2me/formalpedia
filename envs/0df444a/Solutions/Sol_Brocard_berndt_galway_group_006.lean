-- Prove2me | solution 1 for Brocard.berndt_galway_group_006
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:07:06.31171+00:00
-- url     : https://prove2.me/submissions/41192037-0e2c-4ebc-b109-d21547a40e56

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_0235
import Theorems.Thm_Brocard_berndt_galway_chunk_0236
import Theorems.Thm_Brocard_berndt_galway_chunk_0237
import Theorems.Thm_Brocard_berndt_galway_chunk_0238
import Theorems.Thm_Brocard_berndt_galway_chunk_0239
import Theorems.Thm_Brocard_berndt_galway_chunk_0240
import Theorems.Thm_Brocard_berndt_galway_chunk_0241
import Theorems.Thm_Brocard_berndt_galway_chunk_0242
import Theorems.Thm_Brocard_berndt_galway_chunk_0243
import Theorems.Thm_Brocard_berndt_galway_chunk_0244
import Theorems.Thm_Brocard_berndt_galway_chunk_0245
import Theorems.Thm_Brocard_berndt_galway_chunk_0246
import Theorems.Thm_Brocard_berndt_galway_chunk_0247
import Theorems.Thm_Brocard_berndt_galway_chunk_0248
import Theorems.Thm_Brocard_berndt_galway_chunk_0249
import Theorems.Thm_Brocard_berndt_galway_chunk_0250
import Theorems.Thm_Brocard_berndt_galway_chunk_0251
import Theorems.Thm_Brocard_berndt_galway_chunk_0252
import Theorems.Thm_Brocard_berndt_galway_chunk_0253
import Theorems.Thm_Brocard_berndt_galway_chunk_0254
import Theorems.Thm_Brocard_berndt_galway_chunk_0255
import Theorems.Thm_Brocard_berndt_galway_chunk_0256
import Theorems.Thm_Brocard_berndt_galway_chunk_0257
import Theorems.Thm_Brocard_berndt_galway_chunk_0258
import Theorems.Thm_Brocard_berndt_galway_chunk_0259
import Theorems.Thm_Brocard_berndt_galway_chunk_0260
import Theorems.Thm_Brocard_berndt_galway_chunk_0261
import Theorems.Thm_Brocard_berndt_galway_chunk_0262
import Theorems.Thm_Brocard_berndt_galway_chunk_0263
import Theorems.Thm_Brocard_berndt_galway_chunk_0264
import Theorems.Thm_Brocard_berndt_galway_chunk_0265
import Theorems.Thm_Brocard_berndt_galway_chunk_0266
import Theorems.Thm_Brocard_berndt_galway_chunk_0267
import Theorems.Thm_Brocard_berndt_galway_chunk_0268
import Theorems.Thm_Brocard_berndt_galway_chunk_0269
import Theorems.Thm_Brocard_berndt_galway_chunk_0270
import Theorems.Thm_Brocard_berndt_galway_chunk_0271
import Theorems.Thm_Brocard_berndt_galway_chunk_0272
import Theorems.Thm_Brocard_berndt_galway_chunk_0273
import Theorems.Thm_Brocard_berndt_galway_chunk_0274
import Theorems.Thm_Brocard_berndt_galway_chunk_0275
import Theorems.Thm_Brocard_berndt_galway_chunk_0276
import Theorems.Thm_Brocard_berndt_galway_chunk_0277
import Theorems.Thm_Brocard_berndt_galway_chunk_0278
import Theorems.Thm_Brocard_berndt_galway_chunk_0279
import Theorems.Thm_Brocard_berndt_galway_chunk_0280

theorem solution (n m : ℕ) (h1 : 42086335 ≤ n) (h2 : n < 50359716) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 46223025 with hs0 | hs0
  · -- n < 46223025
    rcases Nat.lt_or_ge n 44244608 with hs1 | hs1
    · -- n < 44244608
      rcases Nat.lt_or_ge n 43165472 with hs2 | hs2
      · -- n < 43165472
        rcases Nat.lt_or_ge n 42625903 with hs3 | hs3
        · -- n < 42625903
          rcases Nat.lt_or_ge n 42446047 with hs4 | hs4
          · -- n < 42446047
            rcases Nat.lt_or_ge n 42266191 with hs5 | hs5
            · -- n < 42266191
              exact Brocard.berndt_galway_chunk_0235 n m (by omega) (by omega) h
            · -- n >= 42266191
              exact Brocard.berndt_galway_chunk_0236 n m (by omega) (by omega) h
          · -- n >= 42446047
            exact Brocard.berndt_galway_chunk_0237 n m (by omega) (by omega) h
        · -- n >= 42625903
          rcases Nat.lt_or_ge n 42985616 with hs4 | hs4
          · -- n < 42985616
            rcases Nat.lt_or_ge n 42805759 with hs5 | hs5
            · -- n < 42805759
              exact Brocard.berndt_galway_chunk_0238 n m (by omega) (by omega) h
            · -- n >= 42805759
              exact Brocard.berndt_galway_chunk_0239 n m (by omega) (by omega) h
          · -- n >= 42985616
            exact Brocard.berndt_galway_chunk_0240 n m (by omega) (by omega) h
      · -- n >= 43165472
        rcases Nat.lt_or_ge n 43705040 with hs3 | hs3
        · -- n < 43705040
          rcases Nat.lt_or_ge n 43525184 with hs4 | hs4
          · -- n < 43525184
            rcases Nat.lt_or_ge n 43345328 with hs5 | hs5
            · -- n < 43345328
              exact Brocard.berndt_galway_chunk_0241 n m (by omega) (by omega) h
            · -- n >= 43345328
              exact Brocard.berndt_galway_chunk_0242 n m (by omega) (by omega) h
          · -- n >= 43525184
            exact Brocard.berndt_galway_chunk_0243 n m (by omega) (by omega) h
        · -- n >= 43705040
          rcases Nat.lt_or_ge n 44064752 with hs4 | hs4
          · -- n < 44064752
            rcases Nat.lt_or_ge n 43884896 with hs5 | hs5
            · -- n < 43884896
              exact Brocard.berndt_galway_chunk_0244 n m (by omega) (by omega) h
            · -- n >= 43884896
              exact Brocard.berndt_galway_chunk_0245 n m (by omega) (by omega) h
          · -- n >= 44064752
            exact Brocard.berndt_galway_chunk_0246 n m (by omega) (by omega) h
    · -- n >= 44244608
      rcases Nat.lt_or_ge n 45323745 with hs2 | hs2
      · -- n < 45323745
        rcases Nat.lt_or_ge n 44784177 with hs3 | hs3
        · -- n < 44784177
          rcases Nat.lt_or_ge n 44604320 with hs4 | hs4
          · -- n < 44604320
            rcases Nat.lt_or_ge n 44424464 with hs5 | hs5
            · -- n < 44424464
              exact Brocard.berndt_galway_chunk_0247 n m (by omega) (by omega) h
            · -- n >= 44424464
              exact Brocard.berndt_galway_chunk_0248 n m (by omega) (by omega) h
          · -- n >= 44604320
            exact Brocard.berndt_galway_chunk_0249 n m (by omega) (by omega) h
        · -- n >= 44784177
          rcases Nat.lt_or_ge n 45143889 with hs4 | hs4
          · -- n < 45143889
            rcases Nat.lt_or_ge n 44964033 with hs5 | hs5
            · -- n < 44964033
              exact Brocard.berndt_galway_chunk_0250 n m (by omega) (by omega) h
            · -- n >= 44964033
              exact Brocard.berndt_galway_chunk_0251 n m (by omega) (by omega) h
          · -- n >= 45143889
            exact Brocard.berndt_galway_chunk_0252 n m (by omega) (by omega) h
      · -- n >= 45323745
        rcases Nat.lt_or_ge n 45863313 with hs3 | hs3
        · -- n < 45863313
          rcases Nat.lt_or_ge n 45683457 with hs4 | hs4
          · -- n < 45683457
            rcases Nat.lt_or_ge n 45503601 with hs5 | hs5
            · -- n < 45503601
              exact Brocard.berndt_galway_chunk_0253 n m (by omega) (by omega) h
            · -- n >= 45503601
              exact Brocard.berndt_galway_chunk_0254 n m (by omega) (by omega) h
          · -- n >= 45683457
            exact Brocard.berndt_galway_chunk_0255 n m (by omega) (by omega) h
        · -- n >= 45863313
          rcases Nat.lt_or_ge n 46043169 with hs4 | hs4
          · -- n < 46043169
            exact Brocard.berndt_galway_chunk_0256 n m (by omega) (by omega) h
          · -- n >= 46043169
            exact Brocard.berndt_galway_chunk_0257 n m (by omega) (by omega) h
  · -- n >= 46223025
    rcases Nat.lt_or_ge n 48381299 with hs1 | hs1
    · -- n < 48381299
      rcases Nat.lt_or_ge n 47302162 with hs2 | hs2
      · -- n < 47302162
        rcases Nat.lt_or_ge n 46762594 with hs3 | hs3
        · -- n < 46762594
          rcases Nat.lt_or_ge n 46582738 with hs4 | hs4
          · -- n < 46582738
            rcases Nat.lt_or_ge n 46402881 with hs5 | hs5
            · -- n < 46402881
              exact Brocard.berndt_galway_chunk_0258 n m (by omega) (by omega) h
            · -- n >= 46402881
              exact Brocard.berndt_galway_chunk_0259 n m (by omega) (by omega) h
          · -- n >= 46582738
            exact Brocard.berndt_galway_chunk_0260 n m (by omega) (by omega) h
        · -- n >= 46762594
          rcases Nat.lt_or_ge n 47122306 with hs4 | hs4
          · -- n < 47122306
            rcases Nat.lt_or_ge n 46942450 with hs5 | hs5
            · -- n < 46942450
              exact Brocard.berndt_galway_chunk_0261 n m (by omega) (by omega) h
            · -- n >= 46942450
              exact Brocard.berndt_galway_chunk_0262 n m (by omega) (by omega) h
          · -- n >= 47122306
            exact Brocard.berndt_galway_chunk_0263 n m (by omega) (by omega) h
      · -- n >= 47302162
        rcases Nat.lt_or_ge n 47841730 with hs3 | hs3
        · -- n < 47841730
          rcases Nat.lt_or_ge n 47661874 with hs4 | hs4
          · -- n < 47661874
            rcases Nat.lt_or_ge n 47482018 with hs5 | hs5
            · -- n < 47482018
              exact Brocard.berndt_galway_chunk_0264 n m (by omega) (by omega) h
            · -- n >= 47482018
              exact Brocard.berndt_galway_chunk_0265 n m (by omega) (by omega) h
          · -- n >= 47661874
            exact Brocard.berndt_galway_chunk_0266 n m (by omega) (by omega) h
        · -- n >= 47841730
          rcases Nat.lt_or_ge n 48201442 with hs4 | hs4
          · -- n < 48201442
            rcases Nat.lt_or_ge n 48021586 with hs5 | hs5
            · -- n < 48021586
              exact Brocard.berndt_galway_chunk_0267 n m (by omega) (by omega) h
            · -- n >= 48021586
              exact Brocard.berndt_galway_chunk_0268 n m (by omega) (by omega) h
          · -- n >= 48201442
            exact Brocard.berndt_galway_chunk_0269 n m (by omega) (by omega) h
    · -- n >= 48381299
      rcases Nat.lt_or_ge n 49460435 with hs2 | hs2
      · -- n < 49460435
        rcases Nat.lt_or_ge n 48920867 with hs3 | hs3
        · -- n < 48920867
          rcases Nat.lt_or_ge n 48741011 with hs4 | hs4
          · -- n < 48741011
            rcases Nat.lt_or_ge n 48561155 with hs5 | hs5
            · -- n < 48561155
              exact Brocard.berndt_galway_chunk_0270 n m (by omega) (by omega) h
            · -- n >= 48561155
              exact Brocard.berndt_galway_chunk_0271 n m (by omega) (by omega) h
          · -- n >= 48741011
            exact Brocard.berndt_galway_chunk_0272 n m (by omega) (by omega) h
        · -- n >= 48920867
          rcases Nat.lt_or_ge n 49280579 with hs4 | hs4
          · -- n < 49280579
            rcases Nat.lt_or_ge n 49100723 with hs5 | hs5
            · -- n < 49100723
              exact Brocard.berndt_galway_chunk_0273 n m (by omega) (by omega) h
            · -- n >= 49100723
              exact Brocard.berndt_galway_chunk_0274 n m (by omega) (by omega) h
          · -- n >= 49280579
            exact Brocard.berndt_galway_chunk_0275 n m (by omega) (by omega) h
      · -- n >= 49460435
        rcases Nat.lt_or_ge n 50000004 with hs3 | hs3
        · -- n < 50000004
          rcases Nat.lt_or_ge n 49820147 with hs4 | hs4
          · -- n < 49820147
            rcases Nat.lt_or_ge n 49640291 with hs5 | hs5
            · -- n < 49640291
              exact Brocard.berndt_galway_chunk_0276 n m (by omega) (by omega) h
            · -- n >= 49640291
              exact Brocard.berndt_galway_chunk_0277 n m (by omega) (by omega) h
          · -- n >= 49820147
            exact Brocard.berndt_galway_chunk_0278 n m (by omega) (by omega) h
        · -- n >= 50000004
          rcases Nat.lt_or_ge n 50179860 with hs4 | hs4
          · -- n < 50179860
            exact Brocard.berndt_galway_chunk_0279 n m (by omega) (by omega) h
          · -- n >= 50179860
            exact Brocard.berndt_galway_chunk_0280 n m (by omega) (by omega) h
