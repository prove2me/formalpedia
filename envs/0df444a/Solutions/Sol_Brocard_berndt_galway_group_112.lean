-- Prove2me | solution 1 for Brocard.berndt_galway_group_112
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:11:10.879728+00:00
-- url     : https://prove2.me/submissions/95a2540c-dca9-4c0b-bcfb-4d1ad461d9ea

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_5146
import Theorems.Thm_Brocard_berndt_galway_chunk_5147
import Theorems.Thm_Brocard_berndt_galway_chunk_5148
import Theorems.Thm_Brocard_berndt_galway_chunk_5149
import Theorems.Thm_Brocard_berndt_galway_chunk_5150
import Theorems.Thm_Brocard_berndt_galway_chunk_5151
import Theorems.Thm_Brocard_berndt_galway_chunk_5152
import Theorems.Thm_Brocard_berndt_galway_chunk_5153
import Theorems.Thm_Brocard_berndt_galway_chunk_5154
import Theorems.Thm_Brocard_berndt_galway_chunk_5155
import Theorems.Thm_Brocard_berndt_galway_chunk_5156
import Theorems.Thm_Brocard_berndt_galway_chunk_5157
import Theorems.Thm_Brocard_berndt_galway_chunk_5158
import Theorems.Thm_Brocard_berndt_galway_chunk_5159
import Theorems.Thm_Brocard_berndt_galway_chunk_5160
import Theorems.Thm_Brocard_berndt_galway_chunk_5161
import Theorems.Thm_Brocard_berndt_galway_chunk_5162
import Theorems.Thm_Brocard_berndt_galway_chunk_5163
import Theorems.Thm_Brocard_berndt_galway_chunk_5164
import Theorems.Thm_Brocard_berndt_galway_chunk_5165
import Theorems.Thm_Brocard_berndt_galway_chunk_5166
import Theorems.Thm_Brocard_berndt_galway_chunk_5167
import Theorems.Thm_Brocard_berndt_galway_chunk_5168
import Theorems.Thm_Brocard_berndt_galway_chunk_5169
import Theorems.Thm_Brocard_berndt_galway_chunk_5170
import Theorems.Thm_Brocard_berndt_galway_chunk_5171
import Theorems.Thm_Brocard_berndt_galway_chunk_5172
import Theorems.Thm_Brocard_berndt_galway_chunk_5173
import Theorems.Thm_Brocard_berndt_galway_chunk_5174
import Theorems.Thm_Brocard_berndt_galway_chunk_5175
import Theorems.Thm_Brocard_berndt_galway_chunk_5176
import Theorems.Thm_Brocard_berndt_galway_chunk_5177
import Theorems.Thm_Brocard_berndt_galway_chunk_5178
import Theorems.Thm_Brocard_berndt_galway_chunk_5179
import Theorems.Thm_Brocard_berndt_galway_chunk_5180
import Theorems.Thm_Brocard_berndt_galway_chunk_5181
import Theorems.Thm_Brocard_berndt_galway_chunk_5182
import Theorems.Thm_Brocard_berndt_galway_chunk_5183
import Theorems.Thm_Brocard_berndt_galway_chunk_5184
import Theorems.Thm_Brocard_berndt_galway_chunk_5185
import Theorems.Thm_Brocard_berndt_galway_chunk_5186
import Theorems.Thm_Brocard_berndt_galway_chunk_5187
import Theorems.Thm_Brocard_berndt_galway_chunk_5188
import Theorems.Thm_Brocard_berndt_galway_chunk_5189
import Theorems.Thm_Brocard_berndt_galway_chunk_5190
import Theorems.Thm_Brocard_berndt_galway_chunk_5191
import Theorems.Thm_Brocard_berndt_galway_chunk_5192

theorem solution (n m : ℕ) (h1 : 925359712 ≤ n) (h2 : n < 933812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 929676258 with hs0 | hs0
  · -- n < 929676258
    rcases Nat.lt_or_ge n 927517985 with hs1 | hs1
    · -- n < 927517985
      rcases Nat.lt_or_ge n 926438848 with hs2 | hs2
      · -- n < 926438848
        rcases Nat.lt_or_ge n 925899280 with hs3 | hs3
        · -- n < 925899280
          rcases Nat.lt_or_ge n 925719424 with hs4 | hs4
          · -- n < 925719424
            rcases Nat.lt_or_ge n 925539568 with hs5 | hs5
            · -- n < 925539568
              exact Brocard.berndt_galway_chunk_5146 n m (by omega) (by omega) h
            · -- n >= 925539568
              exact Brocard.berndt_galway_chunk_5147 n m (by omega) (by omega) h
          · -- n >= 925719424
            exact Brocard.berndt_galway_chunk_5148 n m (by omega) (by omega) h
        · -- n >= 925899280
          rcases Nat.lt_or_ge n 926258992 with hs4 | hs4
          · -- n < 926258992
            rcases Nat.lt_or_ge n 926079136 with hs5 | hs5
            · -- n < 926079136
              exact Brocard.berndt_galway_chunk_5149 n m (by omega) (by omega) h
            · -- n >= 926079136
              exact Brocard.berndt_galway_chunk_5150 n m (by omega) (by omega) h
          · -- n >= 926258992
            exact Brocard.berndt_galway_chunk_5151 n m (by omega) (by omega) h
      · -- n >= 926438848
        rcases Nat.lt_or_ge n 926978417 with hs3 | hs3
        · -- n < 926978417
          rcases Nat.lt_or_ge n 926798561 with hs4 | hs4
          · -- n < 926798561
            rcases Nat.lt_or_ge n 926618705 with hs5 | hs5
            · -- n < 926618705
              exact Brocard.berndt_galway_chunk_5152 n m (by omega) (by omega) h
            · -- n >= 926618705
              exact Brocard.berndt_galway_chunk_5153 n m (by omega) (by omega) h
          · -- n >= 926798561
            exact Brocard.berndt_galway_chunk_5154 n m (by omega) (by omega) h
        · -- n >= 926978417
          rcases Nat.lt_or_ge n 927338129 with hs4 | hs4
          · -- n < 927338129
            rcases Nat.lt_or_ge n 927158273 with hs5 | hs5
            · -- n < 927158273
              exact Brocard.berndt_galway_chunk_5155 n m (by omega) (by omega) h
            · -- n >= 927158273
              exact Brocard.berndt_galway_chunk_5156 n m (by omega) (by omega) h
          · -- n >= 927338129
            exact Brocard.berndt_galway_chunk_5157 n m (by omega) (by omega) h
    · -- n >= 927517985
      rcases Nat.lt_or_ge n 928597122 with hs2 | hs2
      · -- n < 928597122
        rcases Nat.lt_or_ge n 928057553 with hs3 | hs3
        · -- n < 928057553
          rcases Nat.lt_or_ge n 927877697 with hs4 | hs4
          · -- n < 927877697
            rcases Nat.lt_or_ge n 927697841 with hs5 | hs5
            · -- n < 927697841
              exact Brocard.berndt_galway_chunk_5158 n m (by omega) (by omega) h
            · -- n >= 927697841
              exact Brocard.berndt_galway_chunk_5159 n m (by omega) (by omega) h
          · -- n >= 927877697
            exact Brocard.berndt_galway_chunk_5160 n m (by omega) (by omega) h
        · -- n >= 928057553
          rcases Nat.lt_or_ge n 928417266 with hs4 | hs4
          · -- n < 928417266
            rcases Nat.lt_or_ge n 928237410 with hs5 | hs5
            · -- n < 928237410
              exact Brocard.berndt_galway_chunk_5161 n m (by omega) (by omega) h
            · -- n >= 928237410
              exact Brocard.berndt_galway_chunk_5162 n m (by omega) (by omega) h
          · -- n >= 928417266
            exact Brocard.berndt_galway_chunk_5163 n m (by omega) (by omega) h
      · -- n >= 928597122
        rcases Nat.lt_or_ge n 929136690 with hs3 | hs3
        · -- n < 929136690
          rcases Nat.lt_or_ge n 928956834 with hs4 | hs4
          · -- n < 928956834
            rcases Nat.lt_or_ge n 928776978 with hs5 | hs5
            · -- n < 928776978
              exact Brocard.berndt_galway_chunk_5164 n m (by omega) (by omega) h
            · -- n >= 928776978
              exact Brocard.berndt_galway_chunk_5165 n m (by omega) (by omega) h
          · -- n >= 928956834
            exact Brocard.berndt_galway_chunk_5166 n m (by omega) (by omega) h
        · -- n >= 929136690
          rcases Nat.lt_or_ge n 929496402 with hs4 | hs4
          · -- n < 929496402
            rcases Nat.lt_or_ge n 929316546 with hs5 | hs5
            · -- n < 929316546
              exact Brocard.berndt_galway_chunk_5167 n m (by omega) (by omega) h
            · -- n >= 929316546
              exact Brocard.berndt_galway_chunk_5168 n m (by omega) (by omega) h
          · -- n >= 929496402
            exact Brocard.berndt_galway_chunk_5169 n m (by omega) (by omega) h
  · -- n >= 929676258
    rcases Nat.lt_or_ge n 931834532 with hs1 | hs1
    · -- n < 931834532
      rcases Nat.lt_or_ge n 930755395 with hs2 | hs2
      · -- n < 930755395
        rcases Nat.lt_or_ge n 930215827 with hs3 | hs3
        · -- n < 930215827
          rcases Nat.lt_or_ge n 930035971 with hs4 | hs4
          · -- n < 930035971
            rcases Nat.lt_or_ge n 929856115 with hs5 | hs5
            · -- n < 929856115
              exact Brocard.berndt_galway_chunk_5170 n m (by omega) (by omega) h
            · -- n >= 929856115
              exact Brocard.berndt_galway_chunk_5171 n m (by omega) (by omega) h
          · -- n >= 930035971
            exact Brocard.berndt_galway_chunk_5172 n m (by omega) (by omega) h
        · -- n >= 930215827
          rcases Nat.lt_or_ge n 930575539 with hs4 | hs4
          · -- n < 930575539
            rcases Nat.lt_or_ge n 930395683 with hs5 | hs5
            · -- n < 930395683
              exact Brocard.berndt_galway_chunk_5173 n m (by omega) (by omega) h
            · -- n >= 930395683
              exact Brocard.berndt_galway_chunk_5174 n m (by omega) (by omega) h
          · -- n >= 930575539
            exact Brocard.berndt_galway_chunk_5175 n m (by omega) (by omega) h
      · -- n >= 930755395
        rcases Nat.lt_or_ge n 931294964 with hs3 | hs3
        · -- n < 931294964
          rcases Nat.lt_or_ge n 931115107 with hs4 | hs4
          · -- n < 931115107
            rcases Nat.lt_or_ge n 930935251 with hs5 | hs5
            · -- n < 930935251
              exact Brocard.berndt_galway_chunk_5176 n m (by omega) (by omega) h
            · -- n >= 930935251
              exact Brocard.berndt_galway_chunk_5177 n m (by omega) (by omega) h
          · -- n >= 931115107
            exact Brocard.berndt_galway_chunk_5178 n m (by omega) (by omega) h
        · -- n >= 931294964
          rcases Nat.lt_or_ge n 931654676 with hs4 | hs4
          · -- n < 931654676
            rcases Nat.lt_or_ge n 931474820 with hs5 | hs5
            · -- n < 931474820
              exact Brocard.berndt_galway_chunk_5179 n m (by omega) (by omega) h
            · -- n >= 931474820
              exact Brocard.berndt_galway_chunk_5180 n m (by omega) (by omega) h
          · -- n >= 931654676
            exact Brocard.berndt_galway_chunk_5181 n m (by omega) (by omega) h
    · -- n >= 931834532
      rcases Nat.lt_or_ge n 932913669 with hs2 | hs2
      · -- n < 932913669
        rcases Nat.lt_or_ge n 932374100 with hs3 | hs3
        · -- n < 932374100
          rcases Nat.lt_or_ge n 932194244 with hs4 | hs4
          · -- n < 932194244
            rcases Nat.lt_or_ge n 932014388 with hs5 | hs5
            · -- n < 932014388
              exact Brocard.berndt_galway_chunk_5182 n m (by omega) (by omega) h
            · -- n >= 932014388
              exact Brocard.berndt_galway_chunk_5183 n m (by omega) (by omega) h
          · -- n >= 932194244
            exact Brocard.berndt_galway_chunk_5184 n m (by omega) (by omega) h
        · -- n >= 932374100
          rcases Nat.lt_or_ge n 932733812 with hs4 | hs4
          · -- n < 932733812
            rcases Nat.lt_or_ge n 932553956 with hs5 | hs5
            · -- n < 932553956
              exact Brocard.berndt_galway_chunk_5185 n m (by omega) (by omega) h
            · -- n >= 932553956
              exact Brocard.berndt_galway_chunk_5186 n m (by omega) (by omega) h
          · -- n >= 932733812
            exact Brocard.berndt_galway_chunk_5187 n m (by omega) (by omega) h
      · -- n >= 932913669
        rcases Nat.lt_or_ge n 933453237 with hs3 | hs3
        · -- n < 933453237
          rcases Nat.lt_or_ge n 933273381 with hs4 | hs4
          · -- n < 933273381
            rcases Nat.lt_or_ge n 933093525 with hs5 | hs5
            · -- n < 933093525
              exact Brocard.berndt_galway_chunk_5188 n m (by omega) (by omega) h
            · -- n >= 933093525
              exact Brocard.berndt_galway_chunk_5189 n m (by omega) (by omega) h
          · -- n >= 933273381
            exact Brocard.berndt_galway_chunk_5190 n m (by omega) (by omega) h
        · -- n >= 933453237
          rcases Nat.lt_or_ge n 933633093 with hs4 | hs4
          · -- n < 933633093
            exact Brocard.berndt_galway_chunk_5191 n m (by omega) (by omega) h
          · -- n >= 933633093
            exact Brocard.berndt_galway_chunk_5192 n m (by omega) (by omega) h
