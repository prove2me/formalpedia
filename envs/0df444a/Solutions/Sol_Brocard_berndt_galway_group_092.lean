-- Prove2me | solution 1 for Brocard.berndt_galway_group_092
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:13:56.380864+00:00
-- url     : https://prove2.me/submissions/f0f1f5be-8e66-472f-9b3b-e9ad8f2ee5f7

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_4219
import Theorems.Thm_Brocard_berndt_galway_chunk_4220
import Theorems.Thm_Brocard_berndt_galway_chunk_4221
import Theorems.Thm_Brocard_berndt_galway_chunk_4222
import Theorems.Thm_Brocard_berndt_galway_chunk_4223
import Theorems.Thm_Brocard_berndt_galway_chunk_4224
import Theorems.Thm_Brocard_berndt_galway_chunk_4225
import Theorems.Thm_Brocard_berndt_galway_chunk_4226
import Theorems.Thm_Brocard_berndt_galway_chunk_4227
import Theorems.Thm_Brocard_berndt_galway_chunk_4228
import Theorems.Thm_Brocard_berndt_galway_chunk_4229
import Theorems.Thm_Brocard_berndt_galway_chunk_4230
import Theorems.Thm_Brocard_berndt_galway_chunk_4231
import Theorems.Thm_Brocard_berndt_galway_chunk_4232
import Theorems.Thm_Brocard_berndt_galway_chunk_4233
import Theorems.Thm_Brocard_berndt_galway_chunk_4234
import Theorems.Thm_Brocard_berndt_galway_chunk_4235
import Theorems.Thm_Brocard_berndt_galway_chunk_4236
import Theorems.Thm_Brocard_berndt_galway_chunk_4237
import Theorems.Thm_Brocard_berndt_galway_chunk_4238
import Theorems.Thm_Brocard_berndt_galway_chunk_4239
import Theorems.Thm_Brocard_berndt_galway_chunk_4240
import Theorems.Thm_Brocard_berndt_galway_chunk_4241
import Theorems.Thm_Brocard_berndt_galway_chunk_4242
import Theorems.Thm_Brocard_berndt_galway_chunk_4243
import Theorems.Thm_Brocard_berndt_galway_chunk_4244
import Theorems.Thm_Brocard_berndt_galway_chunk_4245
import Theorems.Thm_Brocard_berndt_galway_chunk_4246
import Theorems.Thm_Brocard_berndt_galway_chunk_4247
import Theorems.Thm_Brocard_berndt_galway_chunk_4248
import Theorems.Thm_Brocard_berndt_galway_chunk_4249
import Theorems.Thm_Brocard_berndt_galway_chunk_4250
import Theorems.Thm_Brocard_berndt_galway_chunk_4251
import Theorems.Thm_Brocard_berndt_galway_chunk_4252
import Theorems.Thm_Brocard_berndt_galway_chunk_4253
import Theorems.Thm_Brocard_berndt_galway_chunk_4254
import Theorems.Thm_Brocard_berndt_galway_chunk_4255
import Theorems.Thm_Brocard_berndt_galway_chunk_4256
import Theorems.Thm_Brocard_berndt_galway_chunk_4257
import Theorems.Thm_Brocard_berndt_galway_chunk_4258
import Theorems.Thm_Brocard_berndt_galway_chunk_4259
import Theorems.Thm_Brocard_berndt_galway_chunk_4260
import Theorems.Thm_Brocard_berndt_galway_chunk_4261
import Theorems.Thm_Brocard_berndt_galway_chunk_4262
import Theorems.Thm_Brocard_berndt_galway_chunk_4263
import Theorems.Thm_Brocard_berndt_galway_chunk_4264

theorem solution (n m : ℕ) (h1 : 758633093 ≤ n) (h2 : n < 766906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 762769784 with hs0 | hs0
  · -- n < 762769784
    rcases Nat.lt_or_ge n 760791366 with hs1 | hs1
    · -- n < 760791366
      rcases Nat.lt_or_ge n 759712230 with hs2 | hs2
      · -- n < 759712230
        rcases Nat.lt_or_ge n 759172661 with hs3 | hs3
        · -- n < 759172661
          rcases Nat.lt_or_ge n 758992805 with hs4 | hs4
          · -- n < 758992805
            rcases Nat.lt_or_ge n 758812949 with hs5 | hs5
            · -- n < 758812949
              exact Brocard.berndt_galway_chunk_4219 n m (by omega) (by omega) h
            · -- n >= 758812949
              exact Brocard.berndt_galway_chunk_4220 n m (by omega) (by omega) h
          · -- n >= 758992805
            exact Brocard.berndt_galway_chunk_4221 n m (by omega) (by omega) h
        · -- n >= 759172661
          rcases Nat.lt_or_ge n 759532374 with hs4 | hs4
          · -- n < 759532374
            rcases Nat.lt_or_ge n 759352517 with hs5 | hs5
            · -- n < 759352517
              exact Brocard.berndt_galway_chunk_4222 n m (by omega) (by omega) h
            · -- n >= 759352517
              exact Brocard.berndt_galway_chunk_4223 n m (by omega) (by omega) h
          · -- n >= 759532374
            exact Brocard.berndt_galway_chunk_4224 n m (by omega) (by omega) h
      · -- n >= 759712230
        rcases Nat.lt_or_ge n 760251798 with hs3 | hs3
        · -- n < 760251798
          rcases Nat.lt_or_ge n 760071942 with hs4 | hs4
          · -- n < 760071942
            rcases Nat.lt_or_ge n 759892086 with hs5 | hs5
            · -- n < 759892086
              exact Brocard.berndt_galway_chunk_4225 n m (by omega) (by omega) h
            · -- n >= 759892086
              exact Brocard.berndt_galway_chunk_4226 n m (by omega) (by omega) h
          · -- n >= 760071942
            exact Brocard.berndt_galway_chunk_4227 n m (by omega) (by omega) h
        · -- n >= 760251798
          rcases Nat.lt_or_ge n 760611510 with hs4 | hs4
          · -- n < 760611510
            rcases Nat.lt_or_ge n 760431654 with hs5 | hs5
            · -- n < 760431654
              exact Brocard.berndt_galway_chunk_4228 n m (by omega) (by omega) h
            · -- n >= 760431654
              exact Brocard.berndt_galway_chunk_4229 n m (by omega) (by omega) h
          · -- n >= 760611510
            exact Brocard.berndt_galway_chunk_4230 n m (by omega) (by omega) h
    · -- n >= 760791366
      rcases Nat.lt_or_ge n 761870503 with hs2 | hs2
      · -- n < 761870503
        rcases Nat.lt_or_ge n 761330935 with hs3 | hs3
        · -- n < 761330935
          rcases Nat.lt_or_ge n 761151079 with hs4 | hs4
          · -- n < 761151079
            rcases Nat.lt_or_ge n 760971223 with hs5 | hs5
            · -- n < 760971223
              exact Brocard.berndt_galway_chunk_4231 n m (by omega) (by omega) h
            · -- n >= 760971223
              exact Brocard.berndt_galway_chunk_4232 n m (by omega) (by omega) h
          · -- n >= 761151079
            exact Brocard.berndt_galway_chunk_4233 n m (by omega) (by omega) h
        · -- n >= 761330935
          rcases Nat.lt_or_ge n 761690647 with hs4 | hs4
          · -- n < 761690647
            rcases Nat.lt_or_ge n 761510791 with hs5 | hs5
            · -- n < 761510791
              exact Brocard.berndt_galway_chunk_4234 n m (by omega) (by omega) h
            · -- n >= 761510791
              exact Brocard.berndt_galway_chunk_4235 n m (by omega) (by omega) h
          · -- n >= 761690647
            exact Brocard.berndt_galway_chunk_4236 n m (by omega) (by omega) h
      · -- n >= 761870503
        rcases Nat.lt_or_ge n 762410071 with hs3 | hs3
        · -- n < 762410071
          rcases Nat.lt_or_ge n 762230215 with hs4 | hs4
          · -- n < 762230215
            rcases Nat.lt_or_ge n 762050359 with hs5 | hs5
            · -- n < 762050359
              exact Brocard.berndt_galway_chunk_4237 n m (by omega) (by omega) h
            · -- n >= 762050359
              exact Brocard.berndt_galway_chunk_4238 n m (by omega) (by omega) h
          · -- n >= 762230215
            exact Brocard.berndt_galway_chunk_4239 n m (by omega) (by omega) h
        · -- n >= 762410071
          rcases Nat.lt_or_ge n 762589928 with hs4 | hs4
          · -- n < 762589928
            exact Brocard.berndt_galway_chunk_4240 n m (by omega) (by omega) h
          · -- n >= 762589928
            exact Brocard.berndt_galway_chunk_4241 n m (by omega) (by omega) h
  · -- n >= 762769784
    rcases Nat.lt_or_ge n 764928057 with hs1 | hs1
    · -- n < 764928057
      rcases Nat.lt_or_ge n 763848920 with hs2 | hs2
      · -- n < 763848920
        rcases Nat.lt_or_ge n 763309352 with hs3 | hs3
        · -- n < 763309352
          rcases Nat.lt_or_ge n 763129496 with hs4 | hs4
          · -- n < 763129496
            rcases Nat.lt_or_ge n 762949640 with hs5 | hs5
            · -- n < 762949640
              exact Brocard.berndt_galway_chunk_4242 n m (by omega) (by omega) h
            · -- n >= 762949640
              exact Brocard.berndt_galway_chunk_4243 n m (by omega) (by omega) h
          · -- n >= 763129496
            exact Brocard.berndt_galway_chunk_4244 n m (by omega) (by omega) h
        · -- n >= 763309352
          rcases Nat.lt_or_ge n 763669064 with hs4 | hs4
          · -- n < 763669064
            rcases Nat.lt_or_ge n 763489208 with hs5 | hs5
            · -- n < 763489208
              exact Brocard.berndt_galway_chunk_4245 n m (by omega) (by omega) h
            · -- n >= 763489208
              exact Brocard.berndt_galway_chunk_4246 n m (by omega) (by omega) h
          · -- n >= 763669064
            exact Brocard.berndt_galway_chunk_4247 n m (by omega) (by omega) h
      · -- n >= 763848920
        rcases Nat.lt_or_ge n 764388489 with hs3 | hs3
        · -- n < 764388489
          rcases Nat.lt_or_ge n 764208633 with hs4 | hs4
          · -- n < 764208633
            rcases Nat.lt_or_ge n 764028776 with hs5 | hs5
            · -- n < 764028776
              exact Brocard.berndt_galway_chunk_4248 n m (by omega) (by omega) h
            · -- n >= 764028776
              exact Brocard.berndt_galway_chunk_4249 n m (by omega) (by omega) h
          · -- n >= 764208633
            exact Brocard.berndt_galway_chunk_4250 n m (by omega) (by omega) h
        · -- n >= 764388489
          rcases Nat.lt_or_ge n 764748201 with hs4 | hs4
          · -- n < 764748201
            rcases Nat.lt_or_ge n 764568345 with hs5 | hs5
            · -- n < 764568345
              exact Brocard.berndt_galway_chunk_4251 n m (by omega) (by omega) h
            · -- n >= 764568345
              exact Brocard.berndt_galway_chunk_4252 n m (by omega) (by omega) h
          · -- n >= 764748201
            exact Brocard.berndt_galway_chunk_4253 n m (by omega) (by omega) h
    · -- n >= 764928057
      rcases Nat.lt_or_ge n 766007194 with hs2 | hs2
      · -- n < 766007194
        rcases Nat.lt_or_ge n 765467625 with hs3 | hs3
        · -- n < 765467625
          rcases Nat.lt_or_ge n 765287769 with hs4 | hs4
          · -- n < 765287769
            rcases Nat.lt_or_ge n 765107913 with hs5 | hs5
            · -- n < 765107913
              exact Brocard.berndt_galway_chunk_4254 n m (by omega) (by omega) h
            · -- n >= 765107913
              exact Brocard.berndt_galway_chunk_4255 n m (by omega) (by omega) h
          · -- n >= 765287769
            exact Brocard.berndt_galway_chunk_4256 n m (by omega) (by omega) h
        · -- n >= 765467625
          rcases Nat.lt_or_ge n 765827338 with hs4 | hs4
          · -- n < 765827338
            rcases Nat.lt_or_ge n 765647482 with hs5 | hs5
            · -- n < 765647482
              exact Brocard.berndt_galway_chunk_4257 n m (by omega) (by omega) h
            · -- n >= 765647482
              exact Brocard.berndt_galway_chunk_4258 n m (by omega) (by omega) h
          · -- n >= 765827338
            exact Brocard.berndt_galway_chunk_4259 n m (by omega) (by omega) h
      · -- n >= 766007194
        rcases Nat.lt_or_ge n 766546762 with hs3 | hs3
        · -- n < 766546762
          rcases Nat.lt_or_ge n 766366906 with hs4 | hs4
          · -- n < 766366906
            rcases Nat.lt_or_ge n 766187050 with hs5 | hs5
            · -- n < 766187050
              exact Brocard.berndt_galway_chunk_4260 n m (by omega) (by omega) h
            · -- n >= 766187050
              exact Brocard.berndt_galway_chunk_4261 n m (by omega) (by omega) h
          · -- n >= 766366906
            exact Brocard.berndt_galway_chunk_4262 n m (by omega) (by omega) h
        · -- n >= 766546762
          rcases Nat.lt_or_ge n 766726618 with hs4 | hs4
          · -- n < 766726618
            exact Brocard.berndt_galway_chunk_4263 n m (by omega) (by omega) h
          · -- n >= 766726618
            exact Brocard.berndt_galway_chunk_4264 n m (by omega) (by omega) h
