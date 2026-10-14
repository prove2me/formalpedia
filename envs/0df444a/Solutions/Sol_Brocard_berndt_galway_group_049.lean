-- Prove2me | solution 1 for Brocard.berndt_galway_group_049
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:17:44.283647+00:00
-- url     : https://prove2.me/submissions/352c5abb-5ab6-4211-a315-4a3f5aea84a8

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_2225
import Theorems.Thm_Brocard_berndt_galway_chunk_2226
import Theorems.Thm_Brocard_berndt_galway_chunk_2227
import Theorems.Thm_Brocard_berndt_galway_chunk_2228
import Theorems.Thm_Brocard_berndt_galway_chunk_2229
import Theorems.Thm_Brocard_berndt_galway_chunk_2230
import Theorems.Thm_Brocard_berndt_galway_chunk_2231
import Theorems.Thm_Brocard_berndt_galway_chunk_2232
import Theorems.Thm_Brocard_berndt_galway_chunk_2233
import Theorems.Thm_Brocard_berndt_galway_chunk_2234
import Theorems.Thm_Brocard_berndt_galway_chunk_2235
import Theorems.Thm_Brocard_berndt_galway_chunk_2236
import Theorems.Thm_Brocard_berndt_galway_chunk_2237
import Theorems.Thm_Brocard_berndt_galway_chunk_2238
import Theorems.Thm_Brocard_berndt_galway_chunk_2239
import Theorems.Thm_Brocard_berndt_galway_chunk_2240
import Theorems.Thm_Brocard_berndt_galway_chunk_2241
import Theorems.Thm_Brocard_berndt_galway_chunk_2242
import Theorems.Thm_Brocard_berndt_galway_chunk_2243
import Theorems.Thm_Brocard_berndt_galway_chunk_2244
import Theorems.Thm_Brocard_berndt_galway_chunk_2245
import Theorems.Thm_Brocard_berndt_galway_chunk_2246
import Theorems.Thm_Brocard_berndt_galway_chunk_2247
import Theorems.Thm_Brocard_berndt_galway_chunk_2248
import Theorems.Thm_Brocard_berndt_galway_chunk_2249
import Theorems.Thm_Brocard_berndt_galway_chunk_2250
import Theorems.Thm_Brocard_berndt_galway_chunk_2251
import Theorems.Thm_Brocard_berndt_galway_chunk_2252
import Theorems.Thm_Brocard_berndt_galway_chunk_2253
import Theorems.Thm_Brocard_berndt_galway_chunk_2254
import Theorems.Thm_Brocard_berndt_galway_chunk_2255
import Theorems.Thm_Brocard_berndt_galway_chunk_2256
import Theorems.Thm_Brocard_berndt_galway_chunk_2257
import Theorems.Thm_Brocard_berndt_galway_chunk_2258
import Theorems.Thm_Brocard_berndt_galway_chunk_2259
import Theorems.Thm_Brocard_berndt_galway_chunk_2260
import Theorems.Thm_Brocard_berndt_galway_chunk_2261
import Theorems.Thm_Brocard_berndt_galway_chunk_2262
import Theorems.Thm_Brocard_berndt_galway_chunk_2263
import Theorems.Thm_Brocard_berndt_galway_chunk_2264
import Theorems.Thm_Brocard_berndt_galway_chunk_2265
import Theorems.Thm_Brocard_berndt_galway_chunk_2266
import Theorems.Thm_Brocard_berndt_galway_chunk_2267
import Theorems.Thm_Brocard_berndt_galway_chunk_2268
import Theorems.Thm_Brocard_berndt_galway_chunk_2269
import Theorems.Thm_Brocard_berndt_galway_chunk_2270
import Theorems.Thm_Brocard_berndt_galway_chunk_2271

theorem solution (n m : ℕ) (h1 : 400000000 ≤ n) (h2 : n < 408453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 404316546 with hs0 | hs0
  · -- n < 404316546
    rcases Nat.lt_or_ge n 402158273 with hs1 | hs1
    · -- n < 402158273
      rcases Nat.lt_or_ge n 401079136 with hs2 | hs2
      · -- n < 401079136
        rcases Nat.lt_or_ge n 400539568 with hs3 | hs3
        · -- n < 400539568
          rcases Nat.lt_or_ge n 400359712 with hs4 | hs4
          · -- n < 400359712
            rcases Nat.lt_or_ge n 400179856 with hs5 | hs5
            · -- n < 400179856
              exact Brocard.berndt_galway_chunk_2225 n m (by omega) (by omega) h
            · -- n >= 400179856
              exact Brocard.berndt_galway_chunk_2226 n m (by omega) (by omega) h
          · -- n >= 400359712
            exact Brocard.berndt_galway_chunk_2227 n m (by omega) (by omega) h
        · -- n >= 400539568
          rcases Nat.lt_or_ge n 400899280 with hs4 | hs4
          · -- n < 400899280
            rcases Nat.lt_or_ge n 400719424 with hs5 | hs5
            · -- n < 400719424
              exact Brocard.berndt_galway_chunk_2228 n m (by omega) (by omega) h
            · -- n >= 400719424
              exact Brocard.berndt_galway_chunk_2229 n m (by omega) (by omega) h
          · -- n >= 400899280
            exact Brocard.berndt_galway_chunk_2230 n m (by omega) (by omega) h
      · -- n >= 401079136
        rcases Nat.lt_or_ge n 401618705 with hs3 | hs3
        · -- n < 401618705
          rcases Nat.lt_or_ge n 401438848 with hs4 | hs4
          · -- n < 401438848
            rcases Nat.lt_or_ge n 401258992 with hs5 | hs5
            · -- n < 401258992
              exact Brocard.berndt_galway_chunk_2231 n m (by omega) (by omega) h
            · -- n >= 401258992
              exact Brocard.berndt_galway_chunk_2232 n m (by omega) (by omega) h
          · -- n >= 401438848
            exact Brocard.berndt_galway_chunk_2233 n m (by omega) (by omega) h
        · -- n >= 401618705
          rcases Nat.lt_or_ge n 401978417 with hs4 | hs4
          · -- n < 401978417
            rcases Nat.lt_or_ge n 401798561 with hs5 | hs5
            · -- n < 401798561
              exact Brocard.berndt_galway_chunk_2234 n m (by omega) (by omega) h
            · -- n >= 401798561
              exact Brocard.berndt_galway_chunk_2235 n m (by omega) (by omega) h
          · -- n >= 401978417
            exact Brocard.berndt_galway_chunk_2236 n m (by omega) (by omega) h
    · -- n >= 402158273
      rcases Nat.lt_or_ge n 403237410 with hs2 | hs2
      · -- n < 403237410
        rcases Nat.lt_or_ge n 402697841 with hs3 | hs3
        · -- n < 402697841
          rcases Nat.lt_or_ge n 402517985 with hs4 | hs4
          · -- n < 402517985
            rcases Nat.lt_or_ge n 402338129 with hs5 | hs5
            · -- n < 402338129
              exact Brocard.berndt_galway_chunk_2237 n m (by omega) (by omega) h
            · -- n >= 402338129
              exact Brocard.berndt_galway_chunk_2238 n m (by omega) (by omega) h
          · -- n >= 402517985
            exact Brocard.berndt_galway_chunk_2239 n m (by omega) (by omega) h
        · -- n >= 402697841
          rcases Nat.lt_or_ge n 403057553 with hs4 | hs4
          · -- n < 403057553
            rcases Nat.lt_or_ge n 402877697 with hs5 | hs5
            · -- n < 402877697
              exact Brocard.berndt_galway_chunk_2240 n m (by omega) (by omega) h
            · -- n >= 402877697
              exact Brocard.berndt_galway_chunk_2241 n m (by omega) (by omega) h
          · -- n >= 403057553
            exact Brocard.berndt_galway_chunk_2242 n m (by omega) (by omega) h
      · -- n >= 403237410
        rcases Nat.lt_or_ge n 403776978 with hs3 | hs3
        · -- n < 403776978
          rcases Nat.lt_or_ge n 403597122 with hs4 | hs4
          · -- n < 403597122
            rcases Nat.lt_or_ge n 403417266 with hs5 | hs5
            · -- n < 403417266
              exact Brocard.berndt_galway_chunk_2243 n m (by omega) (by omega) h
            · -- n >= 403417266
              exact Brocard.berndt_galway_chunk_2244 n m (by omega) (by omega) h
          · -- n >= 403597122
            exact Brocard.berndt_galway_chunk_2245 n m (by omega) (by omega) h
        · -- n >= 403776978
          rcases Nat.lt_or_ge n 404136690 with hs4 | hs4
          · -- n < 404136690
            rcases Nat.lt_or_ge n 403956834 with hs5 | hs5
            · -- n < 403956834
              exact Brocard.berndt_galway_chunk_2246 n m (by omega) (by omega) h
            · -- n >= 403956834
              exact Brocard.berndt_galway_chunk_2247 n m (by omega) (by omega) h
          · -- n >= 404136690
            exact Brocard.berndt_galway_chunk_2248 n m (by omega) (by omega) h
  · -- n >= 404316546
    rcases Nat.lt_or_ge n 406474820 with hs1 | hs1
    · -- n < 406474820
      rcases Nat.lt_or_ge n 405395683 with hs2 | hs2
      · -- n < 405395683
        rcases Nat.lt_or_ge n 404856115 with hs3 | hs3
        · -- n < 404856115
          rcases Nat.lt_or_ge n 404676258 with hs4 | hs4
          · -- n < 404676258
            rcases Nat.lt_or_ge n 404496402 with hs5 | hs5
            · -- n < 404496402
              exact Brocard.berndt_galway_chunk_2249 n m (by omega) (by omega) h
            · -- n >= 404496402
              exact Brocard.berndt_galway_chunk_2250 n m (by omega) (by omega) h
          · -- n >= 404676258
            exact Brocard.berndt_galway_chunk_2251 n m (by omega) (by omega) h
        · -- n >= 404856115
          rcases Nat.lt_or_ge n 405215827 with hs4 | hs4
          · -- n < 405215827
            rcases Nat.lt_or_ge n 405035971 with hs5 | hs5
            · -- n < 405035971
              exact Brocard.berndt_galway_chunk_2252 n m (by omega) (by omega) h
            · -- n >= 405035971
              exact Brocard.berndt_galway_chunk_2253 n m (by omega) (by omega) h
          · -- n >= 405215827
            exact Brocard.berndt_galway_chunk_2254 n m (by omega) (by omega) h
      · -- n >= 405395683
        rcases Nat.lt_or_ge n 405935251 with hs3 | hs3
        · -- n < 405935251
          rcases Nat.lt_or_ge n 405755395 with hs4 | hs4
          · -- n < 405755395
            rcases Nat.lt_or_ge n 405575539 with hs5 | hs5
            · -- n < 405575539
              exact Brocard.berndt_galway_chunk_2255 n m (by omega) (by omega) h
            · -- n >= 405575539
              exact Brocard.berndt_galway_chunk_2256 n m (by omega) (by omega) h
          · -- n >= 405755395
            exact Brocard.berndt_galway_chunk_2257 n m (by omega) (by omega) h
        · -- n >= 405935251
          rcases Nat.lt_or_ge n 406294964 with hs4 | hs4
          · -- n < 406294964
            rcases Nat.lt_or_ge n 406115107 with hs5 | hs5
            · -- n < 406115107
              exact Brocard.berndt_galway_chunk_2258 n m (by omega) (by omega) h
            · -- n >= 406115107
              exact Brocard.berndt_galway_chunk_2259 n m (by omega) (by omega) h
          · -- n >= 406294964
            exact Brocard.berndt_galway_chunk_2260 n m (by omega) (by omega) h
    · -- n >= 406474820
      rcases Nat.lt_or_ge n 407553956 with hs2 | hs2
      · -- n < 407553956
        rcases Nat.lt_or_ge n 407014388 with hs3 | hs3
        · -- n < 407014388
          rcases Nat.lt_or_ge n 406834532 with hs4 | hs4
          · -- n < 406834532
            rcases Nat.lt_or_ge n 406654676 with hs5 | hs5
            · -- n < 406654676
              exact Brocard.berndt_galway_chunk_2261 n m (by omega) (by omega) h
            · -- n >= 406654676
              exact Brocard.berndt_galway_chunk_2262 n m (by omega) (by omega) h
          · -- n >= 406834532
            exact Brocard.berndt_galway_chunk_2263 n m (by omega) (by omega) h
        · -- n >= 407014388
          rcases Nat.lt_or_ge n 407374100 with hs4 | hs4
          · -- n < 407374100
            rcases Nat.lt_or_ge n 407194244 with hs5 | hs5
            · -- n < 407194244
              exact Brocard.berndt_galway_chunk_2264 n m (by omega) (by omega) h
            · -- n >= 407194244
              exact Brocard.berndt_galway_chunk_2265 n m (by omega) (by omega) h
          · -- n >= 407374100
            exact Brocard.berndt_galway_chunk_2266 n m (by omega) (by omega) h
      · -- n >= 407553956
        rcases Nat.lt_or_ge n 408093525 with hs3 | hs3
        · -- n < 408093525
          rcases Nat.lt_or_ge n 407913669 with hs4 | hs4
          · -- n < 407913669
            rcases Nat.lt_or_ge n 407733812 with hs5 | hs5
            · -- n < 407733812
              exact Brocard.berndt_galway_chunk_2267 n m (by omega) (by omega) h
            · -- n >= 407733812
              exact Brocard.berndt_galway_chunk_2268 n m (by omega) (by omega) h
          · -- n >= 407913669
            exact Brocard.berndt_galway_chunk_2269 n m (by omega) (by omega) h
        · -- n >= 408093525
          rcases Nat.lt_or_ge n 408273381 with hs4 | hs4
          · -- n < 408273381
            exact Brocard.berndt_galway_chunk_2270 n m (by omega) (by omega) h
          · -- n >= 408273381
            exact Brocard.berndt_galway_chunk_2271 n m (by omega) (by omega) h
