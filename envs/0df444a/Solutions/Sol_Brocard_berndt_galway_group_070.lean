-- Prove2me | solution 1 for Brocard.berndt_galway_group_070
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:12:18.255441+00:00
-- url     : https://prove2.me/submissions/a47bcb82-7b48-47e3-84b0-587675d62a32

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_3199
import Theorems.Thm_Brocard_berndt_galway_chunk_3200
import Theorems.Thm_Brocard_berndt_galway_chunk_3201
import Theorems.Thm_Brocard_berndt_galway_chunk_3202
import Theorems.Thm_Brocard_berndt_galway_chunk_3203
import Theorems.Thm_Brocard_berndt_galway_chunk_3204
import Theorems.Thm_Brocard_berndt_galway_chunk_3205
import Theorems.Thm_Brocard_berndt_galway_chunk_3206
import Theorems.Thm_Brocard_berndt_galway_chunk_3207
import Theorems.Thm_Brocard_berndt_galway_chunk_3208
import Theorems.Thm_Brocard_berndt_galway_chunk_3209
import Theorems.Thm_Brocard_berndt_galway_chunk_3210
import Theorems.Thm_Brocard_berndt_galway_chunk_3211
import Theorems.Thm_Brocard_berndt_galway_chunk_3212
import Theorems.Thm_Brocard_berndt_galway_chunk_3213
import Theorems.Thm_Brocard_berndt_galway_chunk_3214
import Theorems.Thm_Brocard_berndt_galway_chunk_3215
import Theorems.Thm_Brocard_berndt_galway_chunk_3216
import Theorems.Thm_Brocard_berndt_galway_chunk_3217
import Theorems.Thm_Brocard_berndt_galway_chunk_3218
import Theorems.Thm_Brocard_berndt_galway_chunk_3219
import Theorems.Thm_Brocard_berndt_galway_chunk_3220
import Theorems.Thm_Brocard_berndt_galway_chunk_3221
import Theorems.Thm_Brocard_berndt_galway_chunk_3222
import Theorems.Thm_Brocard_berndt_galway_chunk_3223
import Theorems.Thm_Brocard_berndt_galway_chunk_3224
import Theorems.Thm_Brocard_berndt_galway_chunk_3225
import Theorems.Thm_Brocard_berndt_galway_chunk_3226
import Theorems.Thm_Brocard_berndt_galway_chunk_3227
import Theorems.Thm_Brocard_berndt_galway_chunk_3228
import Theorems.Thm_Brocard_berndt_galway_chunk_3229
import Theorems.Thm_Brocard_berndt_galway_chunk_3230
import Theorems.Thm_Brocard_berndt_galway_chunk_3231
import Theorems.Thm_Brocard_berndt_galway_chunk_3232
import Theorems.Thm_Brocard_berndt_galway_chunk_3233
import Theorems.Thm_Brocard_berndt_galway_chunk_3234
import Theorems.Thm_Brocard_berndt_galway_chunk_3235
import Theorems.Thm_Brocard_berndt_galway_chunk_3236
import Theorems.Thm_Brocard_berndt_galway_chunk_3237
import Theorems.Thm_Brocard_berndt_galway_chunk_3238
import Theorems.Thm_Brocard_berndt_galway_chunk_3239
import Theorems.Thm_Brocard_berndt_galway_chunk_3240
import Theorems.Thm_Brocard_berndt_galway_chunk_3241
import Theorems.Thm_Brocard_berndt_galway_chunk_3242
import Theorems.Thm_Brocard_berndt_galway_chunk_3243
import Theorems.Thm_Brocard_berndt_galway_chunk_3244

theorem solution (n m : ℕ) (h1 : 575179856 ≤ n) (h2 : n < 583453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 579316546 with hs0 | hs0
  · -- n < 579316546
    rcases Nat.lt_or_ge n 577338129 with hs1 | hs1
    · -- n < 577338129
      rcases Nat.lt_or_ge n 576258992 with hs2 | hs2
      · -- n < 576258992
        rcases Nat.lt_or_ge n 575719424 with hs3 | hs3
        · -- n < 575719424
          rcases Nat.lt_or_ge n 575539568 with hs4 | hs4
          · -- n < 575539568
            rcases Nat.lt_or_ge n 575359712 with hs5 | hs5
            · -- n < 575359712
              exact Brocard.berndt_galway_chunk_3199 n m (by omega) (by omega) h
            · -- n >= 575359712
              exact Brocard.berndt_galway_chunk_3200 n m (by omega) (by omega) h
          · -- n >= 575539568
            exact Brocard.berndt_galway_chunk_3201 n m (by omega) (by omega) h
        · -- n >= 575719424
          rcases Nat.lt_or_ge n 576079136 with hs4 | hs4
          · -- n < 576079136
            rcases Nat.lt_or_ge n 575899280 with hs5 | hs5
            · -- n < 575899280
              exact Brocard.berndt_galway_chunk_3202 n m (by omega) (by omega) h
            · -- n >= 575899280
              exact Brocard.berndt_galway_chunk_3203 n m (by omega) (by omega) h
          · -- n >= 576079136
            exact Brocard.berndt_galway_chunk_3204 n m (by omega) (by omega) h
      · -- n >= 576258992
        rcases Nat.lt_or_ge n 576798561 with hs3 | hs3
        · -- n < 576798561
          rcases Nat.lt_or_ge n 576618705 with hs4 | hs4
          · -- n < 576618705
            rcases Nat.lt_or_ge n 576438848 with hs5 | hs5
            · -- n < 576438848
              exact Brocard.berndt_galway_chunk_3205 n m (by omega) (by omega) h
            · -- n >= 576438848
              exact Brocard.berndt_galway_chunk_3206 n m (by omega) (by omega) h
          · -- n >= 576618705
            exact Brocard.berndt_galway_chunk_3207 n m (by omega) (by omega) h
        · -- n >= 576798561
          rcases Nat.lt_or_ge n 577158273 with hs4 | hs4
          · -- n < 577158273
            rcases Nat.lt_or_ge n 576978417 with hs5 | hs5
            · -- n < 576978417
              exact Brocard.berndt_galway_chunk_3208 n m (by omega) (by omega) h
            · -- n >= 576978417
              exact Brocard.berndt_galway_chunk_3209 n m (by omega) (by omega) h
          · -- n >= 577158273
            exact Brocard.berndt_galway_chunk_3210 n m (by omega) (by omega) h
    · -- n >= 577338129
      rcases Nat.lt_or_ge n 578417266 with hs2 | hs2
      · -- n < 578417266
        rcases Nat.lt_or_ge n 577877697 with hs3 | hs3
        · -- n < 577877697
          rcases Nat.lt_or_ge n 577697841 with hs4 | hs4
          · -- n < 577697841
            rcases Nat.lt_or_ge n 577517985 with hs5 | hs5
            · -- n < 577517985
              exact Brocard.berndt_galway_chunk_3211 n m (by omega) (by omega) h
            · -- n >= 577517985
              exact Brocard.berndt_galway_chunk_3212 n m (by omega) (by omega) h
          · -- n >= 577697841
            exact Brocard.berndt_galway_chunk_3213 n m (by omega) (by omega) h
        · -- n >= 577877697
          rcases Nat.lt_or_ge n 578237410 with hs4 | hs4
          · -- n < 578237410
            rcases Nat.lt_or_ge n 578057553 with hs5 | hs5
            · -- n < 578057553
              exact Brocard.berndt_galway_chunk_3214 n m (by omega) (by omega) h
            · -- n >= 578057553
              exact Brocard.berndt_galway_chunk_3215 n m (by omega) (by omega) h
          · -- n >= 578237410
            exact Brocard.berndt_galway_chunk_3216 n m (by omega) (by omega) h
      · -- n >= 578417266
        rcases Nat.lt_or_ge n 578956834 with hs3 | hs3
        · -- n < 578956834
          rcases Nat.lt_or_ge n 578776978 with hs4 | hs4
          · -- n < 578776978
            rcases Nat.lt_or_ge n 578597122 with hs5 | hs5
            · -- n < 578597122
              exact Brocard.berndt_galway_chunk_3217 n m (by omega) (by omega) h
            · -- n >= 578597122
              exact Brocard.berndt_galway_chunk_3218 n m (by omega) (by omega) h
          · -- n >= 578776978
            exact Brocard.berndt_galway_chunk_3219 n m (by omega) (by omega) h
        · -- n >= 578956834
          rcases Nat.lt_or_ge n 579136690 with hs4 | hs4
          · -- n < 579136690
            exact Brocard.berndt_galway_chunk_3220 n m (by omega) (by omega) h
          · -- n >= 579136690
            exact Brocard.berndt_galway_chunk_3221 n m (by omega) (by omega) h
  · -- n >= 579316546
    rcases Nat.lt_or_ge n 581474820 with hs1 | hs1
    · -- n < 581474820
      rcases Nat.lt_or_ge n 580395683 with hs2 | hs2
      · -- n < 580395683
        rcases Nat.lt_or_ge n 579856115 with hs3 | hs3
        · -- n < 579856115
          rcases Nat.lt_or_ge n 579676258 with hs4 | hs4
          · -- n < 579676258
            rcases Nat.lt_or_ge n 579496402 with hs5 | hs5
            · -- n < 579496402
              exact Brocard.berndt_galway_chunk_3222 n m (by omega) (by omega) h
            · -- n >= 579496402
              exact Brocard.berndt_galway_chunk_3223 n m (by omega) (by omega) h
          · -- n >= 579676258
            exact Brocard.berndt_galway_chunk_3224 n m (by omega) (by omega) h
        · -- n >= 579856115
          rcases Nat.lt_or_ge n 580215827 with hs4 | hs4
          · -- n < 580215827
            rcases Nat.lt_or_ge n 580035971 with hs5 | hs5
            · -- n < 580035971
              exact Brocard.berndt_galway_chunk_3225 n m (by omega) (by omega) h
            · -- n >= 580035971
              exact Brocard.berndt_galway_chunk_3226 n m (by omega) (by omega) h
          · -- n >= 580215827
            exact Brocard.berndt_galway_chunk_3227 n m (by omega) (by omega) h
      · -- n >= 580395683
        rcases Nat.lt_or_ge n 580935251 with hs3 | hs3
        · -- n < 580935251
          rcases Nat.lt_or_ge n 580755395 with hs4 | hs4
          · -- n < 580755395
            rcases Nat.lt_or_ge n 580575539 with hs5 | hs5
            · -- n < 580575539
              exact Brocard.berndt_galway_chunk_3228 n m (by omega) (by omega) h
            · -- n >= 580575539
              exact Brocard.berndt_galway_chunk_3229 n m (by omega) (by omega) h
          · -- n >= 580755395
            exact Brocard.berndt_galway_chunk_3230 n m (by omega) (by omega) h
        · -- n >= 580935251
          rcases Nat.lt_or_ge n 581294964 with hs4 | hs4
          · -- n < 581294964
            rcases Nat.lt_or_ge n 581115107 with hs5 | hs5
            · -- n < 581115107
              exact Brocard.berndt_galway_chunk_3231 n m (by omega) (by omega) h
            · -- n >= 581115107
              exact Brocard.berndt_galway_chunk_3232 n m (by omega) (by omega) h
          · -- n >= 581294964
            exact Brocard.berndt_galway_chunk_3233 n m (by omega) (by omega) h
    · -- n >= 581474820
      rcases Nat.lt_or_ge n 582553956 with hs2 | hs2
      · -- n < 582553956
        rcases Nat.lt_or_ge n 582014388 with hs3 | hs3
        · -- n < 582014388
          rcases Nat.lt_or_ge n 581834532 with hs4 | hs4
          · -- n < 581834532
            rcases Nat.lt_or_ge n 581654676 with hs5 | hs5
            · -- n < 581654676
              exact Brocard.berndt_galway_chunk_3234 n m (by omega) (by omega) h
            · -- n >= 581654676
              exact Brocard.berndt_galway_chunk_3235 n m (by omega) (by omega) h
          · -- n >= 581834532
            exact Brocard.berndt_galway_chunk_3236 n m (by omega) (by omega) h
        · -- n >= 582014388
          rcases Nat.lt_or_ge n 582374100 with hs4 | hs4
          · -- n < 582374100
            rcases Nat.lt_or_ge n 582194244 with hs5 | hs5
            · -- n < 582194244
              exact Brocard.berndt_galway_chunk_3237 n m (by omega) (by omega) h
            · -- n >= 582194244
              exact Brocard.berndt_galway_chunk_3238 n m (by omega) (by omega) h
          · -- n >= 582374100
            exact Brocard.berndt_galway_chunk_3239 n m (by omega) (by omega) h
      · -- n >= 582553956
        rcases Nat.lt_or_ge n 583093525 with hs3 | hs3
        · -- n < 583093525
          rcases Nat.lt_or_ge n 582913669 with hs4 | hs4
          · -- n < 582913669
            rcases Nat.lt_or_ge n 582733812 with hs5 | hs5
            · -- n < 582733812
              exact Brocard.berndt_galway_chunk_3240 n m (by omega) (by omega) h
            · -- n >= 582733812
              exact Brocard.berndt_galway_chunk_3241 n m (by omega) (by omega) h
          · -- n >= 582913669
            exact Brocard.berndt_galway_chunk_3242 n m (by omega) (by omega) h
        · -- n >= 583093525
          rcases Nat.lt_or_ge n 583273381 with hs4 | hs4
          · -- n < 583273381
            exact Brocard.berndt_galway_chunk_3243 n m (by omega) (by omega) h
          · -- n >= 583273381
            exact Brocard.berndt_galway_chunk_3244 n m (by omega) (by omega) h
