-- Prove2me | solution 1 for Brocard.berndt_galway_group_091
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:04:22.293928+00:00
-- url     : https://prove2.me/submissions/6facf427-3aab-4ce7-ac41-0907d6839a58

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_4173
import Theorems.Thm_Brocard_berndt_galway_chunk_4174
import Theorems.Thm_Brocard_berndt_galway_chunk_4175
import Theorems.Thm_Brocard_berndt_galway_chunk_4176
import Theorems.Thm_Brocard_berndt_galway_chunk_4177
import Theorems.Thm_Brocard_berndt_galway_chunk_4178
import Theorems.Thm_Brocard_berndt_galway_chunk_4179
import Theorems.Thm_Brocard_berndt_galway_chunk_4180
import Theorems.Thm_Brocard_berndt_galway_chunk_4181
import Theorems.Thm_Brocard_berndt_galway_chunk_4182
import Theorems.Thm_Brocard_berndt_galway_chunk_4183
import Theorems.Thm_Brocard_berndt_galway_chunk_4184
import Theorems.Thm_Brocard_berndt_galway_chunk_4185
import Theorems.Thm_Brocard_berndt_galway_chunk_4186
import Theorems.Thm_Brocard_berndt_galway_chunk_4187
import Theorems.Thm_Brocard_berndt_galway_chunk_4188
import Theorems.Thm_Brocard_berndt_galway_chunk_4189
import Theorems.Thm_Brocard_berndt_galway_chunk_4190
import Theorems.Thm_Brocard_berndt_galway_chunk_4191
import Theorems.Thm_Brocard_berndt_galway_chunk_4192
import Theorems.Thm_Brocard_berndt_galway_chunk_4193
import Theorems.Thm_Brocard_berndt_galway_chunk_4194
import Theorems.Thm_Brocard_berndt_galway_chunk_4195
import Theorems.Thm_Brocard_berndt_galway_chunk_4196
import Theorems.Thm_Brocard_berndt_galway_chunk_4197
import Theorems.Thm_Brocard_berndt_galway_chunk_4198
import Theorems.Thm_Brocard_berndt_galway_chunk_4199
import Theorems.Thm_Brocard_berndt_galway_chunk_4200
import Theorems.Thm_Brocard_berndt_galway_chunk_4201
import Theorems.Thm_Brocard_berndt_galway_chunk_4202
import Theorems.Thm_Brocard_berndt_galway_chunk_4203
import Theorems.Thm_Brocard_berndt_galway_chunk_4204
import Theorems.Thm_Brocard_berndt_galway_chunk_4205
import Theorems.Thm_Brocard_berndt_galway_chunk_4206
import Theorems.Thm_Brocard_berndt_galway_chunk_4207
import Theorems.Thm_Brocard_berndt_galway_chunk_4208
import Theorems.Thm_Brocard_berndt_galway_chunk_4209
import Theorems.Thm_Brocard_berndt_galway_chunk_4210
import Theorems.Thm_Brocard_berndt_galway_chunk_4211
import Theorems.Thm_Brocard_berndt_galway_chunk_4212
import Theorems.Thm_Brocard_berndt_galway_chunk_4213
import Theorems.Thm_Brocard_berndt_galway_chunk_4214
import Theorems.Thm_Brocard_berndt_galway_chunk_4215
import Theorems.Thm_Brocard_berndt_galway_chunk_4216
import Theorems.Thm_Brocard_berndt_galway_chunk_4217
import Theorems.Thm_Brocard_berndt_galway_chunk_4218

theorem solution (n m : ℕ) (h1 : 750359712 ≤ n) (h2 : n < 758633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 754496402 with hs0 | hs0
  · -- n < 754496402
    rcases Nat.lt_or_ge n 752517985 with hs1 | hs1
    · -- n < 752517985
      rcases Nat.lt_or_ge n 751438848 with hs2 | hs2
      · -- n < 751438848
        rcases Nat.lt_or_ge n 750899280 with hs3 | hs3
        · -- n < 750899280
          rcases Nat.lt_or_ge n 750719424 with hs4 | hs4
          · -- n < 750719424
            rcases Nat.lt_or_ge n 750539568 with hs5 | hs5
            · -- n < 750539568
              exact Brocard.berndt_galway_chunk_4173 n m (by omega) (by omega) h
            · -- n >= 750539568
              exact Brocard.berndt_galway_chunk_4174 n m (by omega) (by omega) h
          · -- n >= 750719424
            exact Brocard.berndt_galway_chunk_4175 n m (by omega) (by omega) h
        · -- n >= 750899280
          rcases Nat.lt_or_ge n 751258992 with hs4 | hs4
          · -- n < 751258992
            rcases Nat.lt_or_ge n 751079136 with hs5 | hs5
            · -- n < 751079136
              exact Brocard.berndt_galway_chunk_4176 n m (by omega) (by omega) h
            · -- n >= 751079136
              exact Brocard.berndt_galway_chunk_4177 n m (by omega) (by omega) h
          · -- n >= 751258992
            exact Brocard.berndt_galway_chunk_4178 n m (by omega) (by omega) h
      · -- n >= 751438848
        rcases Nat.lt_or_ge n 751978417 with hs3 | hs3
        · -- n < 751978417
          rcases Nat.lt_or_ge n 751798561 with hs4 | hs4
          · -- n < 751798561
            rcases Nat.lt_or_ge n 751618705 with hs5 | hs5
            · -- n < 751618705
              exact Brocard.berndt_galway_chunk_4179 n m (by omega) (by omega) h
            · -- n >= 751618705
              exact Brocard.berndt_galway_chunk_4180 n m (by omega) (by omega) h
          · -- n >= 751798561
            exact Brocard.berndt_galway_chunk_4181 n m (by omega) (by omega) h
        · -- n >= 751978417
          rcases Nat.lt_or_ge n 752338129 with hs4 | hs4
          · -- n < 752338129
            rcases Nat.lt_or_ge n 752158273 with hs5 | hs5
            · -- n < 752158273
              exact Brocard.berndt_galway_chunk_4182 n m (by omega) (by omega) h
            · -- n >= 752158273
              exact Brocard.berndt_galway_chunk_4183 n m (by omega) (by omega) h
          · -- n >= 752338129
            exact Brocard.berndt_galway_chunk_4184 n m (by omega) (by omega) h
    · -- n >= 752517985
      rcases Nat.lt_or_ge n 753597122 with hs2 | hs2
      · -- n < 753597122
        rcases Nat.lt_or_ge n 753057553 with hs3 | hs3
        · -- n < 753057553
          rcases Nat.lt_or_ge n 752877697 with hs4 | hs4
          · -- n < 752877697
            rcases Nat.lt_or_ge n 752697841 with hs5 | hs5
            · -- n < 752697841
              exact Brocard.berndt_galway_chunk_4185 n m (by omega) (by omega) h
            · -- n >= 752697841
              exact Brocard.berndt_galway_chunk_4186 n m (by omega) (by omega) h
          · -- n >= 752877697
            exact Brocard.berndt_galway_chunk_4187 n m (by omega) (by omega) h
        · -- n >= 753057553
          rcases Nat.lt_or_ge n 753417266 with hs4 | hs4
          · -- n < 753417266
            rcases Nat.lt_or_ge n 753237410 with hs5 | hs5
            · -- n < 753237410
              exact Brocard.berndt_galway_chunk_4188 n m (by omega) (by omega) h
            · -- n >= 753237410
              exact Brocard.berndt_galway_chunk_4189 n m (by omega) (by omega) h
          · -- n >= 753417266
            exact Brocard.berndt_galway_chunk_4190 n m (by omega) (by omega) h
      · -- n >= 753597122
        rcases Nat.lt_or_ge n 754136690 with hs3 | hs3
        · -- n < 754136690
          rcases Nat.lt_or_ge n 753956834 with hs4 | hs4
          · -- n < 753956834
            rcases Nat.lt_or_ge n 753776978 with hs5 | hs5
            · -- n < 753776978
              exact Brocard.berndt_galway_chunk_4191 n m (by omega) (by omega) h
            · -- n >= 753776978
              exact Brocard.berndt_galway_chunk_4192 n m (by omega) (by omega) h
          · -- n >= 753956834
            exact Brocard.berndt_galway_chunk_4193 n m (by omega) (by omega) h
        · -- n >= 754136690
          rcases Nat.lt_or_ge n 754316546 with hs4 | hs4
          · -- n < 754316546
            exact Brocard.berndt_galway_chunk_4194 n m (by omega) (by omega) h
          · -- n >= 754316546
            exact Brocard.berndt_galway_chunk_4195 n m (by omega) (by omega) h
  · -- n >= 754496402
    rcases Nat.lt_or_ge n 756654676 with hs1 | hs1
    · -- n < 756654676
      rcases Nat.lt_or_ge n 755575539 with hs2 | hs2
      · -- n < 755575539
        rcases Nat.lt_or_ge n 755035971 with hs3 | hs3
        · -- n < 755035971
          rcases Nat.lt_or_ge n 754856115 with hs4 | hs4
          · -- n < 754856115
            rcases Nat.lt_or_ge n 754676258 with hs5 | hs5
            · -- n < 754676258
              exact Brocard.berndt_galway_chunk_4196 n m (by omega) (by omega) h
            · -- n >= 754676258
              exact Brocard.berndt_galway_chunk_4197 n m (by omega) (by omega) h
          · -- n >= 754856115
            exact Brocard.berndt_galway_chunk_4198 n m (by omega) (by omega) h
        · -- n >= 755035971
          rcases Nat.lt_or_ge n 755395683 with hs4 | hs4
          · -- n < 755395683
            rcases Nat.lt_or_ge n 755215827 with hs5 | hs5
            · -- n < 755215827
              exact Brocard.berndt_galway_chunk_4199 n m (by omega) (by omega) h
            · -- n >= 755215827
              exact Brocard.berndt_galway_chunk_4200 n m (by omega) (by omega) h
          · -- n >= 755395683
            exact Brocard.berndt_galway_chunk_4201 n m (by omega) (by omega) h
      · -- n >= 755575539
        rcases Nat.lt_or_ge n 756115107 with hs3 | hs3
        · -- n < 756115107
          rcases Nat.lt_or_ge n 755935251 with hs4 | hs4
          · -- n < 755935251
            rcases Nat.lt_or_ge n 755755395 with hs5 | hs5
            · -- n < 755755395
              exact Brocard.berndt_galway_chunk_4202 n m (by omega) (by omega) h
            · -- n >= 755755395
              exact Brocard.berndt_galway_chunk_4203 n m (by omega) (by omega) h
          · -- n >= 755935251
            exact Brocard.berndt_galway_chunk_4204 n m (by omega) (by omega) h
        · -- n >= 756115107
          rcases Nat.lt_or_ge n 756474820 with hs4 | hs4
          · -- n < 756474820
            rcases Nat.lt_or_ge n 756294964 with hs5 | hs5
            · -- n < 756294964
              exact Brocard.berndt_galway_chunk_4205 n m (by omega) (by omega) h
            · -- n >= 756294964
              exact Brocard.berndt_galway_chunk_4206 n m (by omega) (by omega) h
          · -- n >= 756474820
            exact Brocard.berndt_galway_chunk_4207 n m (by omega) (by omega) h
    · -- n >= 756654676
      rcases Nat.lt_or_ge n 757733812 with hs2 | hs2
      · -- n < 757733812
        rcases Nat.lt_or_ge n 757194244 with hs3 | hs3
        · -- n < 757194244
          rcases Nat.lt_or_ge n 757014388 with hs4 | hs4
          · -- n < 757014388
            rcases Nat.lt_or_ge n 756834532 with hs5 | hs5
            · -- n < 756834532
              exact Brocard.berndt_galway_chunk_4208 n m (by omega) (by omega) h
            · -- n >= 756834532
              exact Brocard.berndt_galway_chunk_4209 n m (by omega) (by omega) h
          · -- n >= 757014388
            exact Brocard.berndt_galway_chunk_4210 n m (by omega) (by omega) h
        · -- n >= 757194244
          rcases Nat.lt_or_ge n 757553956 with hs4 | hs4
          · -- n < 757553956
            rcases Nat.lt_or_ge n 757374100 with hs5 | hs5
            · -- n < 757374100
              exact Brocard.berndt_galway_chunk_4211 n m (by omega) (by omega) h
            · -- n >= 757374100
              exact Brocard.berndt_galway_chunk_4212 n m (by omega) (by omega) h
          · -- n >= 757553956
            exact Brocard.berndt_galway_chunk_4213 n m (by omega) (by omega) h
      · -- n >= 757733812
        rcases Nat.lt_or_ge n 758273381 with hs3 | hs3
        · -- n < 758273381
          rcases Nat.lt_or_ge n 758093525 with hs4 | hs4
          · -- n < 758093525
            rcases Nat.lt_or_ge n 757913669 with hs5 | hs5
            · -- n < 757913669
              exact Brocard.berndt_galway_chunk_4214 n m (by omega) (by omega) h
            · -- n >= 757913669
              exact Brocard.berndt_galway_chunk_4215 n m (by omega) (by omega) h
          · -- n >= 758093525
            exact Brocard.berndt_galway_chunk_4216 n m (by omega) (by omega) h
        · -- n >= 758273381
          rcases Nat.lt_or_ge n 758453237 with hs4 | hs4
          · -- n < 758453237
            exact Brocard.berndt_galway_chunk_4217 n m (by omega) (by omega) h
          · -- n >= 758453237
            exact Brocard.berndt_galway_chunk_4218 n m (by omega) (by omega) h
