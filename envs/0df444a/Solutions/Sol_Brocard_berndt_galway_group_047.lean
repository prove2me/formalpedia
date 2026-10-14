-- Prove2me | solution 1 for Brocard.berndt_galway_group_047
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:02:46.443759+00:00
-- url     : https://prove2.me/submissions/49cf778d-9698-4e3f-9339-c07ecc99b6aa

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_2133
import Theorems.Thm_Brocard_berndt_galway_chunk_2134
import Theorems.Thm_Brocard_berndt_galway_chunk_2135
import Theorems.Thm_Brocard_berndt_galway_chunk_2136
import Theorems.Thm_Brocard_berndt_galway_chunk_2137
import Theorems.Thm_Brocard_berndt_galway_chunk_2138
import Theorems.Thm_Brocard_berndt_galway_chunk_2139
import Theorems.Thm_Brocard_berndt_galway_chunk_2140
import Theorems.Thm_Brocard_berndt_galway_chunk_2141
import Theorems.Thm_Brocard_berndt_galway_chunk_2142
import Theorems.Thm_Brocard_berndt_galway_chunk_2143
import Theorems.Thm_Brocard_berndt_galway_chunk_2144
import Theorems.Thm_Brocard_berndt_galway_chunk_2145
import Theorems.Thm_Brocard_berndt_galway_chunk_2146
import Theorems.Thm_Brocard_berndt_galway_chunk_2147
import Theorems.Thm_Brocard_berndt_galway_chunk_2148
import Theorems.Thm_Brocard_berndt_galway_chunk_2149
import Theorems.Thm_Brocard_berndt_galway_chunk_2150
import Theorems.Thm_Brocard_berndt_galway_chunk_2151
import Theorems.Thm_Brocard_berndt_galway_chunk_2152
import Theorems.Thm_Brocard_berndt_galway_chunk_2153
import Theorems.Thm_Brocard_berndt_galway_chunk_2154
import Theorems.Thm_Brocard_berndt_galway_chunk_2155
import Theorems.Thm_Brocard_berndt_galway_chunk_2156
import Theorems.Thm_Brocard_berndt_galway_chunk_2157
import Theorems.Thm_Brocard_berndt_galway_chunk_2158
import Theorems.Thm_Brocard_berndt_galway_chunk_2159
import Theorems.Thm_Brocard_berndt_galway_chunk_2160
import Theorems.Thm_Brocard_berndt_galway_chunk_2161
import Theorems.Thm_Brocard_berndt_galway_chunk_2162
import Theorems.Thm_Brocard_berndt_galway_chunk_2163
import Theorems.Thm_Brocard_berndt_galway_chunk_2164
import Theorems.Thm_Brocard_berndt_galway_chunk_2165
import Theorems.Thm_Brocard_berndt_galway_chunk_2166
import Theorems.Thm_Brocard_berndt_galway_chunk_2167
import Theorems.Thm_Brocard_berndt_galway_chunk_2168
import Theorems.Thm_Brocard_berndt_galway_chunk_2169
import Theorems.Thm_Brocard_berndt_galway_chunk_2170
import Theorems.Thm_Brocard_berndt_galway_chunk_2171
import Theorems.Thm_Brocard_berndt_galway_chunk_2172
import Theorems.Thm_Brocard_berndt_galway_chunk_2173
import Theorems.Thm_Brocard_berndt_galway_chunk_2174
import Theorems.Thm_Brocard_berndt_galway_chunk_2175
import Theorems.Thm_Brocard_berndt_galway_chunk_2176
import Theorems.Thm_Brocard_berndt_galway_chunk_2177
import Theorems.Thm_Brocard_berndt_galway_chunk_2178

theorem solution (n m : ℕ) (h1 : 383453237 ≤ n) (h2 : n < 391726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 387589928 with hs0 | hs0
  · -- n < 387589928
    rcases Nat.lt_or_ge n 385611510 with hs1 | hs1
    · -- n < 385611510
      rcases Nat.lt_or_ge n 384532374 with hs2 | hs2
      · -- n < 384532374
        rcases Nat.lt_or_ge n 383992805 with hs3 | hs3
        · -- n < 383992805
          rcases Nat.lt_or_ge n 383812949 with hs4 | hs4
          · -- n < 383812949
            rcases Nat.lt_or_ge n 383633093 with hs5 | hs5
            · -- n < 383633093
              exact Brocard.berndt_galway_chunk_2133 n m (by omega) (by omega) h
            · -- n >= 383633093
              exact Brocard.berndt_galway_chunk_2134 n m (by omega) (by omega) h
          · -- n >= 383812949
            exact Brocard.berndt_galway_chunk_2135 n m (by omega) (by omega) h
        · -- n >= 383992805
          rcases Nat.lt_or_ge n 384352517 with hs4 | hs4
          · -- n < 384352517
            rcases Nat.lt_or_ge n 384172661 with hs5 | hs5
            · -- n < 384172661
              exact Brocard.berndt_galway_chunk_2136 n m (by omega) (by omega) h
            · -- n >= 384172661
              exact Brocard.berndt_galway_chunk_2137 n m (by omega) (by omega) h
          · -- n >= 384352517
            exact Brocard.berndt_galway_chunk_2138 n m (by omega) (by omega) h
      · -- n >= 384532374
        rcases Nat.lt_or_ge n 385071942 with hs3 | hs3
        · -- n < 385071942
          rcases Nat.lt_or_ge n 384892086 with hs4 | hs4
          · -- n < 384892086
            rcases Nat.lt_or_ge n 384712230 with hs5 | hs5
            · -- n < 384712230
              exact Brocard.berndt_galway_chunk_2139 n m (by omega) (by omega) h
            · -- n >= 384712230
              exact Brocard.berndt_galway_chunk_2140 n m (by omega) (by omega) h
          · -- n >= 384892086
            exact Brocard.berndt_galway_chunk_2141 n m (by omega) (by omega) h
        · -- n >= 385071942
          rcases Nat.lt_or_ge n 385431654 with hs4 | hs4
          · -- n < 385431654
            rcases Nat.lt_or_ge n 385251798 with hs5 | hs5
            · -- n < 385251798
              exact Brocard.berndt_galway_chunk_2142 n m (by omega) (by omega) h
            · -- n >= 385251798
              exact Brocard.berndt_galway_chunk_2143 n m (by omega) (by omega) h
          · -- n >= 385431654
            exact Brocard.berndt_galway_chunk_2144 n m (by omega) (by omega) h
    · -- n >= 385611510
      rcases Nat.lt_or_ge n 386690647 with hs2 | hs2
      · -- n < 386690647
        rcases Nat.lt_or_ge n 386151079 with hs3 | hs3
        · -- n < 386151079
          rcases Nat.lt_or_ge n 385971223 with hs4 | hs4
          · -- n < 385971223
            rcases Nat.lt_or_ge n 385791366 with hs5 | hs5
            · -- n < 385791366
              exact Brocard.berndt_galway_chunk_2145 n m (by omega) (by omega) h
            · -- n >= 385791366
              exact Brocard.berndt_galway_chunk_2146 n m (by omega) (by omega) h
          · -- n >= 385971223
            exact Brocard.berndt_galway_chunk_2147 n m (by omega) (by omega) h
        · -- n >= 386151079
          rcases Nat.lt_or_ge n 386510791 with hs4 | hs4
          · -- n < 386510791
            rcases Nat.lt_or_ge n 386330935 with hs5 | hs5
            · -- n < 386330935
              exact Brocard.berndt_galway_chunk_2148 n m (by omega) (by omega) h
            · -- n >= 386330935
              exact Brocard.berndt_galway_chunk_2149 n m (by omega) (by omega) h
          · -- n >= 386510791
            exact Brocard.berndt_galway_chunk_2150 n m (by omega) (by omega) h
      · -- n >= 386690647
        rcases Nat.lt_or_ge n 387230215 with hs3 | hs3
        · -- n < 387230215
          rcases Nat.lt_or_ge n 387050359 with hs4 | hs4
          · -- n < 387050359
            rcases Nat.lt_or_ge n 386870503 with hs5 | hs5
            · -- n < 386870503
              exact Brocard.berndt_galway_chunk_2151 n m (by omega) (by omega) h
            · -- n >= 386870503
              exact Brocard.berndt_galway_chunk_2152 n m (by omega) (by omega) h
          · -- n >= 387050359
            exact Brocard.berndt_galway_chunk_2153 n m (by omega) (by omega) h
        · -- n >= 387230215
          rcases Nat.lt_or_ge n 387410071 with hs4 | hs4
          · -- n < 387410071
            exact Brocard.berndt_galway_chunk_2154 n m (by omega) (by omega) h
          · -- n >= 387410071
            exact Brocard.berndt_galway_chunk_2155 n m (by omega) (by omega) h
  · -- n >= 387589928
    rcases Nat.lt_or_ge n 389748201 with hs1 | hs1
    · -- n < 389748201
      rcases Nat.lt_or_ge n 388669064 with hs2 | hs2
      · -- n < 388669064
        rcases Nat.lt_or_ge n 388129496 with hs3 | hs3
        · -- n < 388129496
          rcases Nat.lt_or_ge n 387949640 with hs4 | hs4
          · -- n < 387949640
            rcases Nat.lt_or_ge n 387769784 with hs5 | hs5
            · -- n < 387769784
              exact Brocard.berndt_galway_chunk_2156 n m (by omega) (by omega) h
            · -- n >= 387769784
              exact Brocard.berndt_galway_chunk_2157 n m (by omega) (by omega) h
          · -- n >= 387949640
            exact Brocard.berndt_galway_chunk_2158 n m (by omega) (by omega) h
        · -- n >= 388129496
          rcases Nat.lt_or_ge n 388489208 with hs4 | hs4
          · -- n < 388489208
            rcases Nat.lt_or_ge n 388309352 with hs5 | hs5
            · -- n < 388309352
              exact Brocard.berndt_galway_chunk_2159 n m (by omega) (by omega) h
            · -- n >= 388309352
              exact Brocard.berndt_galway_chunk_2160 n m (by omega) (by omega) h
          · -- n >= 388489208
            exact Brocard.berndt_galway_chunk_2161 n m (by omega) (by omega) h
      · -- n >= 388669064
        rcases Nat.lt_or_ge n 389208633 with hs3 | hs3
        · -- n < 389208633
          rcases Nat.lt_or_ge n 389028776 with hs4 | hs4
          · -- n < 389028776
            rcases Nat.lt_or_ge n 388848920 with hs5 | hs5
            · -- n < 388848920
              exact Brocard.berndt_galway_chunk_2162 n m (by omega) (by omega) h
            · -- n >= 388848920
              exact Brocard.berndt_galway_chunk_2163 n m (by omega) (by omega) h
          · -- n >= 389028776
            exact Brocard.berndt_galway_chunk_2164 n m (by omega) (by omega) h
        · -- n >= 389208633
          rcases Nat.lt_or_ge n 389568345 with hs4 | hs4
          · -- n < 389568345
            rcases Nat.lt_or_ge n 389388489 with hs5 | hs5
            · -- n < 389388489
              exact Brocard.berndt_galway_chunk_2165 n m (by omega) (by omega) h
            · -- n >= 389388489
              exact Brocard.berndt_galway_chunk_2166 n m (by omega) (by omega) h
          · -- n >= 389568345
            exact Brocard.berndt_galway_chunk_2167 n m (by omega) (by omega) h
    · -- n >= 389748201
      rcases Nat.lt_or_ge n 390827338 with hs2 | hs2
      · -- n < 390827338
        rcases Nat.lt_or_ge n 390287769 with hs3 | hs3
        · -- n < 390287769
          rcases Nat.lt_or_ge n 390107913 with hs4 | hs4
          · -- n < 390107913
            rcases Nat.lt_or_ge n 389928057 with hs5 | hs5
            · -- n < 389928057
              exact Brocard.berndt_galway_chunk_2168 n m (by omega) (by omega) h
            · -- n >= 389928057
              exact Brocard.berndt_galway_chunk_2169 n m (by omega) (by omega) h
          · -- n >= 390107913
            exact Brocard.berndt_galway_chunk_2170 n m (by omega) (by omega) h
        · -- n >= 390287769
          rcases Nat.lt_or_ge n 390647482 with hs4 | hs4
          · -- n < 390647482
            rcases Nat.lt_or_ge n 390467625 with hs5 | hs5
            · -- n < 390467625
              exact Brocard.berndt_galway_chunk_2171 n m (by omega) (by omega) h
            · -- n >= 390467625
              exact Brocard.berndt_galway_chunk_2172 n m (by omega) (by omega) h
          · -- n >= 390647482
            exact Brocard.berndt_galway_chunk_2173 n m (by omega) (by omega) h
      · -- n >= 390827338
        rcases Nat.lt_or_ge n 391366906 with hs3 | hs3
        · -- n < 391366906
          rcases Nat.lt_or_ge n 391187050 with hs4 | hs4
          · -- n < 391187050
            rcases Nat.lt_or_ge n 391007194 with hs5 | hs5
            · -- n < 391007194
              exact Brocard.berndt_galway_chunk_2174 n m (by omega) (by omega) h
            · -- n >= 391007194
              exact Brocard.berndt_galway_chunk_2175 n m (by omega) (by omega) h
          · -- n >= 391187050
            exact Brocard.berndt_galway_chunk_2176 n m (by omega) (by omega) h
        · -- n >= 391366906
          rcases Nat.lt_or_ge n 391546762 with hs4 | hs4
          · -- n < 391546762
            exact Brocard.berndt_galway_chunk_2177 n m (by omega) (by omega) h
          · -- n >= 391546762
            exact Brocard.berndt_galway_chunk_2178 n m (by omega) (by omega) h
