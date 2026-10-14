-- Prove2me | solution 1 for Brocard.berndt_galway_group_004
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:30:34.787982+00:00
-- url     : https://prove2.me/submissions/e4f36d52-7d08-42f6-b81e-791c8f300bc9

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_0142
import Theorems.Thm_Brocard_berndt_galway_chunk_0143
import Theorems.Thm_Brocard_berndt_galway_chunk_0144
import Theorems.Thm_Brocard_berndt_galway_chunk_0145
import Theorems.Thm_Brocard_berndt_galway_chunk_0146
import Theorems.Thm_Brocard_berndt_galway_chunk_0147
import Theorems.Thm_Brocard_berndt_galway_chunk_0148
import Theorems.Thm_Brocard_berndt_galway_chunk_0149
import Theorems.Thm_Brocard_berndt_galway_chunk_0150
import Theorems.Thm_Brocard_berndt_galway_chunk_0151
import Theorems.Thm_Brocard_berndt_galway_chunk_0152
import Theorems.Thm_Brocard_berndt_galway_chunk_0153
import Theorems.Thm_Brocard_berndt_galway_chunk_0154
import Theorems.Thm_Brocard_berndt_galway_chunk_0155
import Theorems.Thm_Brocard_berndt_galway_chunk_0156
import Theorems.Thm_Brocard_berndt_galway_chunk_0157
import Theorems.Thm_Brocard_berndt_galway_chunk_0158
import Theorems.Thm_Brocard_berndt_galway_chunk_0159
import Theorems.Thm_Brocard_berndt_galway_chunk_0160
import Theorems.Thm_Brocard_berndt_galway_chunk_0161
import Theorems.Thm_Brocard_berndt_galway_chunk_0162
import Theorems.Thm_Brocard_berndt_galway_chunk_0163
import Theorems.Thm_Brocard_berndt_galway_chunk_0164
import Theorems.Thm_Brocard_berndt_galway_chunk_0165
import Theorems.Thm_Brocard_berndt_galway_chunk_0166
import Theorems.Thm_Brocard_berndt_galway_chunk_0167
import Theorems.Thm_Brocard_berndt_galway_chunk_0168
import Theorems.Thm_Brocard_berndt_galway_chunk_0169
import Theorems.Thm_Brocard_berndt_galway_chunk_0170
import Theorems.Thm_Brocard_berndt_galway_chunk_0171
import Theorems.Thm_Brocard_berndt_galway_chunk_0172
import Theorems.Thm_Brocard_berndt_galway_chunk_0173
import Theorems.Thm_Brocard_berndt_galway_chunk_0174
import Theorems.Thm_Brocard_berndt_galway_chunk_0175
import Theorems.Thm_Brocard_berndt_galway_chunk_0176
import Theorems.Thm_Brocard_berndt_galway_chunk_0177
import Theorems.Thm_Brocard_berndt_galway_chunk_0178
import Theorems.Thm_Brocard_berndt_galway_chunk_0179
import Theorems.Thm_Brocard_berndt_galway_chunk_0180
import Theorems.Thm_Brocard_berndt_galway_chunk_0181
import Theorems.Thm_Brocard_berndt_galway_chunk_0182
import Theorems.Thm_Brocard_berndt_galway_chunk_0183
import Theorems.Thm_Brocard_berndt_galway_chunk_0184
import Theorems.Thm_Brocard_berndt_galway_chunk_0185
import Theorems.Thm_Brocard_berndt_galway_chunk_0186
import Theorems.Thm_Brocard_berndt_galway_chunk_0187
import Theorems.Thm_Brocard_berndt_galway_chunk_0188

theorem solution (n m : ℕ) (h1 : 25359718 ≤ n) (h2 : n < 33812954) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 29676264 with hs0 | hs0
  · -- n < 29676264
    rcases Nat.lt_or_ge n 27517991 with hs1 | hs1
    · -- n < 27517991
      rcases Nat.lt_or_ge n 26438854 with hs2 | hs2
      · -- n < 26438854
        rcases Nat.lt_or_ge n 25899286 with hs3 | hs3
        · -- n < 25899286
          rcases Nat.lt_or_ge n 25719430 with hs4 | hs4
          · -- n < 25719430
            rcases Nat.lt_or_ge n 25539574 with hs5 | hs5
            · -- n < 25539574
              exact Brocard.berndt_galway_chunk_0142 n m (by omega) (by omega) h
            · -- n >= 25539574
              exact Brocard.berndt_galway_chunk_0143 n m (by omega) (by omega) h
          · -- n >= 25719430
            exact Brocard.berndt_galway_chunk_0144 n m (by omega) (by omega) h
        · -- n >= 25899286
          rcases Nat.lt_or_ge n 26258998 with hs4 | hs4
          · -- n < 26258998
            rcases Nat.lt_or_ge n 26079142 with hs5 | hs5
            · -- n < 26079142
              exact Brocard.berndt_galway_chunk_0145 n m (by omega) (by omega) h
            · -- n >= 26079142
              exact Brocard.berndt_galway_chunk_0146 n m (by omega) (by omega) h
          · -- n >= 26258998
            exact Brocard.berndt_galway_chunk_0147 n m (by omega) (by omega) h
      · -- n >= 26438854
        rcases Nat.lt_or_ge n 26978423 with hs3 | hs3
        · -- n < 26978423
          rcases Nat.lt_or_ge n 26798567 with hs4 | hs4
          · -- n < 26798567
            rcases Nat.lt_or_ge n 26618710 with hs5 | hs5
            · -- n < 26618710
              exact Brocard.berndt_galway_chunk_0148 n m (by omega) (by omega) h
            · -- n >= 26618710
              exact Brocard.berndt_galway_chunk_0149 n m (by omega) (by omega) h
          · -- n >= 26798567
            exact Brocard.berndt_galway_chunk_0150 n m (by omega) (by omega) h
        · -- n >= 26978423
          rcases Nat.lt_or_ge n 27338135 with hs4 | hs4
          · -- n < 27338135
            rcases Nat.lt_or_ge n 27158279 with hs5 | hs5
            · -- n < 27158279
              exact Brocard.berndt_galway_chunk_0151 n m (by omega) (by omega) h
            · -- n >= 27158279
              exact Brocard.berndt_galway_chunk_0152 n m (by omega) (by omega) h
          · -- n >= 27338135
            exact Brocard.berndt_galway_chunk_0153 n m (by omega) (by omega) h
    · -- n >= 27517991
      rcases Nat.lt_or_ge n 28597128 with hs2 | hs2
      · -- n < 28597128
        rcases Nat.lt_or_ge n 28057559 with hs3 | hs3
        · -- n < 28057559
          rcases Nat.lt_or_ge n 27877703 with hs4 | hs4
          · -- n < 27877703
            rcases Nat.lt_or_ge n 27697847 with hs5 | hs5
            · -- n < 27697847
              exact Brocard.berndt_galway_chunk_0154 n m (by omega) (by omega) h
            · -- n >= 27697847
              exact Brocard.berndt_galway_chunk_0155 n m (by omega) (by omega) h
          · -- n >= 27877703
            exact Brocard.berndt_galway_chunk_0156 n m (by omega) (by omega) h
        · -- n >= 28057559
          rcases Nat.lt_or_ge n 28417271 with hs4 | hs4
          · -- n < 28417271
            rcases Nat.lt_or_ge n 28237415 with hs5 | hs5
            · -- n < 28237415
              exact Brocard.berndt_galway_chunk_0157 n m (by omega) (by omega) h
            · -- n >= 28237415
              exact Brocard.berndt_galway_chunk_0158 n m (by omega) (by omega) h
          · -- n >= 28417271
            exact Brocard.berndt_galway_chunk_0159 n m (by omega) (by omega) h
      · -- n >= 28597128
        rcases Nat.lt_or_ge n 29136696 with hs3 | hs3
        · -- n < 29136696
          rcases Nat.lt_or_ge n 28956840 with hs4 | hs4
          · -- n < 28956840
            rcases Nat.lt_or_ge n 28776984 with hs5 | hs5
            · -- n < 28776984
              exact Brocard.berndt_galway_chunk_0160 n m (by omega) (by omega) h
            · -- n >= 28776984
              exact Brocard.berndt_galway_chunk_0161 n m (by omega) (by omega) h
          · -- n >= 28956840
            exact Brocard.berndt_galway_chunk_0162 n m (by omega) (by omega) h
        · -- n >= 29136696
          rcases Nat.lt_or_ge n 29496408 with hs4 | hs4
          · -- n < 29496408
            rcases Nat.lt_or_ge n 29316552 with hs5 | hs5
            · -- n < 29316552
              exact Brocard.berndt_galway_chunk_0163 n m (by omega) (by omega) h
            · -- n >= 29316552
              exact Brocard.berndt_galway_chunk_0164 n m (by omega) (by omega) h
          · -- n >= 29496408
            exact Brocard.berndt_galway_chunk_0165 n m (by omega) (by omega) h
  · -- n >= 29676264
    rcases Nat.lt_or_ge n 31834537 with hs1 | hs1
    · -- n < 31834537
      rcases Nat.lt_or_ge n 30755401 with hs2 | hs2
      · -- n < 30755401
        rcases Nat.lt_or_ge n 30215832 with hs3 | hs3
        · -- n < 30215832
          rcases Nat.lt_or_ge n 30035976 with hs4 | hs4
          · -- n < 30035976
            rcases Nat.lt_or_ge n 29856120 with hs5 | hs5
            · -- n < 29856120
              exact Brocard.berndt_galway_chunk_0166 n m (by omega) (by omega) h
            · -- n >= 29856120
              exact Brocard.berndt_galway_chunk_0167 n m (by omega) (by omega) h
          · -- n >= 30035976
            exact Brocard.berndt_galway_chunk_0168 n m (by omega) (by omega) h
        · -- n >= 30215832
          rcases Nat.lt_or_ge n 30575545 with hs4 | hs4
          · -- n < 30575545
            rcases Nat.lt_or_ge n 30395689 with hs5 | hs5
            · -- n < 30395689
              exact Brocard.berndt_galway_chunk_0169 n m (by omega) (by omega) h
            · -- n >= 30395689
              exact Brocard.berndt_galway_chunk_0170 n m (by omega) (by omega) h
          · -- n >= 30575545
            exact Brocard.berndt_galway_chunk_0171 n m (by omega) (by omega) h
      · -- n >= 30755401
        rcases Nat.lt_or_ge n 31294969 with hs3 | hs3
        · -- n < 31294969
          rcases Nat.lt_or_ge n 31115113 with hs4 | hs4
          · -- n < 31115113
            rcases Nat.lt_or_ge n 30935257 with hs5 | hs5
            · -- n < 30935257
              exact Brocard.berndt_galway_chunk_0172 n m (by omega) (by omega) h
            · -- n >= 30935257
              exact Brocard.berndt_galway_chunk_0173 n m (by omega) (by omega) h
          · -- n >= 31115113
            exact Brocard.berndt_galway_chunk_0174 n m (by omega) (by omega) h
        · -- n >= 31294969
          rcases Nat.lt_or_ge n 31654681 with hs4 | hs4
          · -- n < 31654681
            rcases Nat.lt_or_ge n 31474825 with hs5 | hs5
            · -- n < 31474825
              exact Brocard.berndt_galway_chunk_0175 n m (by omega) (by omega) h
            · -- n >= 31474825
              exact Brocard.berndt_galway_chunk_0176 n m (by omega) (by omega) h
          · -- n >= 31654681
            exact Brocard.berndt_galway_chunk_0177 n m (by omega) (by omega) h
    · -- n >= 31834537
      rcases Nat.lt_or_ge n 32913674 with hs2 | hs2
      · -- n < 32913674
        rcases Nat.lt_or_ge n 32374106 with hs3 | hs3
        · -- n < 32374106
          rcases Nat.lt_or_ge n 32194250 with hs4 | hs4
          · -- n < 32194250
            rcases Nat.lt_or_ge n 32014393 with hs5 | hs5
            · -- n < 32014393
              exact Brocard.berndt_galway_chunk_0178 n m (by omega) (by omega) h
            · -- n >= 32014393
              exact Brocard.berndt_galway_chunk_0179 n m (by omega) (by omega) h
          · -- n >= 32194250
            exact Brocard.berndt_galway_chunk_0180 n m (by omega) (by omega) h
        · -- n >= 32374106
          rcases Nat.lt_or_ge n 32733818 with hs4 | hs4
          · -- n < 32733818
            rcases Nat.lt_or_ge n 32553962 with hs5 | hs5
            · -- n < 32553962
              exact Brocard.berndt_galway_chunk_0181 n m (by omega) (by omega) h
            · -- n >= 32553962
              exact Brocard.berndt_galway_chunk_0182 n m (by omega) (by omega) h
          · -- n >= 32733818
            exact Brocard.berndt_galway_chunk_0183 n m (by omega) (by omega) h
      · -- n >= 32913674
        rcases Nat.lt_or_ge n 33453242 with hs3 | hs3
        · -- n < 33453242
          rcases Nat.lt_or_ge n 33273386 with hs4 | hs4
          · -- n < 33273386
            rcases Nat.lt_or_ge n 33093530 with hs5 | hs5
            · -- n < 33093530
              exact Brocard.berndt_galway_chunk_0184 n m (by omega) (by omega) h
            · -- n >= 33093530
              exact Brocard.berndt_galway_chunk_0185 n m (by omega) (by omega) h
          · -- n >= 33273386
            exact Brocard.berndt_galway_chunk_0186 n m (by omega) (by omega) h
        · -- n >= 33453242
          rcases Nat.lt_or_ge n 33633098 with hs4 | hs4
          · -- n < 33633098
            exact Brocard.berndt_galway_chunk_0187 n m (by omega) (by omega) h
          · -- n >= 33633098
            exact Brocard.berndt_galway_chunk_0188 n m (by omega) (by omega) h
