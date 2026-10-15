-- Prove2me | solution 1 for Brocard.berndt_galway_group_116
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:46:22.474454+00:00
-- url     : https://prove2.me/submissions/79a6e183-5710-4c83-a335-e8c2a830c155

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_5331
import Theorems.Thm_Brocard_berndt_galway_chunk_5332
import Theorems.Thm_Brocard_berndt_galway_chunk_5333
import Theorems.Thm_Brocard_berndt_galway_chunk_5334
import Theorems.Thm_Brocard_berndt_galway_chunk_5335
import Theorems.Thm_Brocard_berndt_galway_chunk_5336
import Theorems.Thm_Brocard_berndt_galway_chunk_5337
import Theorems.Thm_Brocard_berndt_galway_chunk_5338
import Theorems.Thm_Brocard_berndt_galway_chunk_5339
import Theorems.Thm_Brocard_berndt_galway_chunk_5340
import Theorems.Thm_Brocard_berndt_galway_chunk_5341
import Theorems.Thm_Brocard_berndt_galway_chunk_5342
import Theorems.Thm_Brocard_berndt_galway_chunk_5343
import Theorems.Thm_Brocard_berndt_galway_chunk_5344
import Theorems.Thm_Brocard_berndt_galway_chunk_5345
import Theorems.Thm_Brocard_berndt_galway_chunk_5346
import Theorems.Thm_Brocard_berndt_galway_chunk_5347
import Theorems.Thm_Brocard_berndt_galway_chunk_5348
import Theorems.Thm_Brocard_berndt_galway_chunk_5349
import Theorems.Thm_Brocard_berndt_galway_chunk_5350
import Theorems.Thm_Brocard_berndt_galway_chunk_5351
import Theorems.Thm_Brocard_berndt_galway_chunk_5352
import Theorems.Thm_Brocard_berndt_galway_chunk_5353
import Theorems.Thm_Brocard_berndt_galway_chunk_5354
import Theorems.Thm_Brocard_berndt_galway_chunk_5355
import Theorems.Thm_Brocard_berndt_galway_chunk_5356
import Theorems.Thm_Brocard_berndt_galway_chunk_5357
import Theorems.Thm_Brocard_berndt_galway_chunk_5358
import Theorems.Thm_Brocard_berndt_galway_chunk_5359
import Theorems.Thm_Brocard_berndt_galway_chunk_5360
import Theorems.Thm_Brocard_berndt_galway_chunk_5361
import Theorems.Thm_Brocard_berndt_galway_chunk_5362
import Theorems.Thm_Brocard_berndt_galway_chunk_5363
import Theorems.Thm_Brocard_berndt_galway_chunk_5364
import Theorems.Thm_Brocard_berndt_galway_chunk_5365
import Theorems.Thm_Brocard_berndt_galway_chunk_5366
import Theorems.Thm_Brocard_berndt_galway_chunk_5367
import Theorems.Thm_Brocard_berndt_galway_chunk_5368
import Theorems.Thm_Brocard_berndt_galway_chunk_5369
import Theorems.Thm_Brocard_berndt_galway_chunk_5370
import Theorems.Thm_Brocard_berndt_galway_chunk_5371
import Theorems.Thm_Brocard_berndt_galway_chunk_5372
import Theorems.Thm_Brocard_berndt_galway_chunk_5373
import Theorems.Thm_Brocard_berndt_galway_chunk_5374
import Theorems.Thm_Brocard_berndt_galway_chunk_5375
import Theorems.Thm_Brocard_berndt_galway_chunk_5376

theorem solution (n m : ℕ) (h1 : 958633093 ≤ n) (h2 : n < 966906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 962769784 with hs0 | hs0
  · -- n < 962769784
    rcases Nat.lt_or_ge n 960791366 with hs1 | hs1
    · -- n < 960791366
      rcases Nat.lt_or_ge n 959712230 with hs2 | hs2
      · -- n < 959712230
        rcases Nat.lt_or_ge n 959172661 with hs3 | hs3
        · -- n < 959172661
          rcases Nat.lt_or_ge n 958992805 with hs4 | hs4
          · -- n < 958992805
            rcases Nat.lt_or_ge n 958812949 with hs5 | hs5
            · -- n < 958812949
              exact Brocard.berndt_galway_chunk_5331 n m (by omega) (by omega) h
            · -- n >= 958812949
              exact Brocard.berndt_galway_chunk_5332 n m (by omega) (by omega) h
          · -- n >= 958992805
            exact Brocard.berndt_galway_chunk_5333 n m (by omega) (by omega) h
        · -- n >= 959172661
          rcases Nat.lt_or_ge n 959532374 with hs4 | hs4
          · -- n < 959532374
            rcases Nat.lt_or_ge n 959352517 with hs5 | hs5
            · -- n < 959352517
              exact Brocard.berndt_galway_chunk_5334 n m (by omega) (by omega) h
            · -- n >= 959352517
              exact Brocard.berndt_galway_chunk_5335 n m (by omega) (by omega) h
          · -- n >= 959532374
            exact Brocard.berndt_galway_chunk_5336 n m (by omega) (by omega) h
      · -- n >= 959712230
        rcases Nat.lt_or_ge n 960251798 with hs3 | hs3
        · -- n < 960251798
          rcases Nat.lt_or_ge n 960071942 with hs4 | hs4
          · -- n < 960071942
            rcases Nat.lt_or_ge n 959892086 with hs5 | hs5
            · -- n < 959892086
              exact Brocard.berndt_galway_chunk_5337 n m (by omega) (by omega) h
            · -- n >= 959892086
              exact Brocard.berndt_galway_chunk_5338 n m (by omega) (by omega) h
          · -- n >= 960071942
            exact Brocard.berndt_galway_chunk_5339 n m (by omega) (by omega) h
        · -- n >= 960251798
          rcases Nat.lt_or_ge n 960611510 with hs4 | hs4
          · -- n < 960611510
            rcases Nat.lt_or_ge n 960431654 with hs5 | hs5
            · -- n < 960431654
              exact Brocard.berndt_galway_chunk_5340 n m (by omega) (by omega) h
            · -- n >= 960431654
              exact Brocard.berndt_galway_chunk_5341 n m (by omega) (by omega) h
          · -- n >= 960611510
            exact Brocard.berndt_galway_chunk_5342 n m (by omega) (by omega) h
    · -- n >= 960791366
      rcases Nat.lt_or_ge n 961870503 with hs2 | hs2
      · -- n < 961870503
        rcases Nat.lt_or_ge n 961330935 with hs3 | hs3
        · -- n < 961330935
          rcases Nat.lt_or_ge n 961151079 with hs4 | hs4
          · -- n < 961151079
            rcases Nat.lt_or_ge n 960971223 with hs5 | hs5
            · -- n < 960971223
              exact Brocard.berndt_galway_chunk_5343 n m (by omega) (by omega) h
            · -- n >= 960971223
              exact Brocard.berndt_galway_chunk_5344 n m (by omega) (by omega) h
          · -- n >= 961151079
            exact Brocard.berndt_galway_chunk_5345 n m (by omega) (by omega) h
        · -- n >= 961330935
          rcases Nat.lt_or_ge n 961690647 with hs4 | hs4
          · -- n < 961690647
            rcases Nat.lt_or_ge n 961510791 with hs5 | hs5
            · -- n < 961510791
              exact Brocard.berndt_galway_chunk_5346 n m (by omega) (by omega) h
            · -- n >= 961510791
              exact Brocard.berndt_galway_chunk_5347 n m (by omega) (by omega) h
          · -- n >= 961690647
            exact Brocard.berndt_galway_chunk_5348 n m (by omega) (by omega) h
      · -- n >= 961870503
        rcases Nat.lt_or_ge n 962410071 with hs3 | hs3
        · -- n < 962410071
          rcases Nat.lt_or_ge n 962230215 with hs4 | hs4
          · -- n < 962230215
            rcases Nat.lt_or_ge n 962050359 with hs5 | hs5
            · -- n < 962050359
              exact Brocard.berndt_galway_chunk_5349 n m (by omega) (by omega) h
            · -- n >= 962050359
              exact Brocard.berndt_galway_chunk_5350 n m (by omega) (by omega) h
          · -- n >= 962230215
            exact Brocard.berndt_galway_chunk_5351 n m (by omega) (by omega) h
        · -- n >= 962410071
          rcases Nat.lt_or_ge n 962589928 with hs4 | hs4
          · -- n < 962589928
            exact Brocard.berndt_galway_chunk_5352 n m (by omega) (by omega) h
          · -- n >= 962589928
            exact Brocard.berndt_galway_chunk_5353 n m (by omega) (by omega) h
  · -- n >= 962769784
    rcases Nat.lt_or_ge n 964928057 with hs1 | hs1
    · -- n < 964928057
      rcases Nat.lt_or_ge n 963848920 with hs2 | hs2
      · -- n < 963848920
        rcases Nat.lt_or_ge n 963309352 with hs3 | hs3
        · -- n < 963309352
          rcases Nat.lt_or_ge n 963129496 with hs4 | hs4
          · -- n < 963129496
            rcases Nat.lt_or_ge n 962949640 with hs5 | hs5
            · -- n < 962949640
              exact Brocard.berndt_galway_chunk_5354 n m (by omega) (by omega) h
            · -- n >= 962949640
              exact Brocard.berndt_galway_chunk_5355 n m (by omega) (by omega) h
          · -- n >= 963129496
            exact Brocard.berndt_galway_chunk_5356 n m (by omega) (by omega) h
        · -- n >= 963309352
          rcases Nat.lt_or_ge n 963669064 with hs4 | hs4
          · -- n < 963669064
            rcases Nat.lt_or_ge n 963489208 with hs5 | hs5
            · -- n < 963489208
              exact Brocard.berndt_galway_chunk_5357 n m (by omega) (by omega) h
            · -- n >= 963489208
              exact Brocard.berndt_galway_chunk_5358 n m (by omega) (by omega) h
          · -- n >= 963669064
            exact Brocard.berndt_galway_chunk_5359 n m (by omega) (by omega) h
      · -- n >= 963848920
        rcases Nat.lt_or_ge n 964388489 with hs3 | hs3
        · -- n < 964388489
          rcases Nat.lt_or_ge n 964208633 with hs4 | hs4
          · -- n < 964208633
            rcases Nat.lt_or_ge n 964028776 with hs5 | hs5
            · -- n < 964028776
              exact Brocard.berndt_galway_chunk_5360 n m (by omega) (by omega) h
            · -- n >= 964028776
              exact Brocard.berndt_galway_chunk_5361 n m (by omega) (by omega) h
          · -- n >= 964208633
            exact Brocard.berndt_galway_chunk_5362 n m (by omega) (by omega) h
        · -- n >= 964388489
          rcases Nat.lt_or_ge n 964748201 with hs4 | hs4
          · -- n < 964748201
            rcases Nat.lt_or_ge n 964568345 with hs5 | hs5
            · -- n < 964568345
              exact Brocard.berndt_galway_chunk_5363 n m (by omega) (by omega) h
            · -- n >= 964568345
              exact Brocard.berndt_galway_chunk_5364 n m (by omega) (by omega) h
          · -- n >= 964748201
            exact Brocard.berndt_galway_chunk_5365 n m (by omega) (by omega) h
    · -- n >= 964928057
      rcases Nat.lt_or_ge n 966007194 with hs2 | hs2
      · -- n < 966007194
        rcases Nat.lt_or_ge n 965467625 with hs3 | hs3
        · -- n < 965467625
          rcases Nat.lt_or_ge n 965287769 with hs4 | hs4
          · -- n < 965287769
            rcases Nat.lt_or_ge n 965107913 with hs5 | hs5
            · -- n < 965107913
              exact Brocard.berndt_galway_chunk_5366 n m (by omega) (by omega) h
            · -- n >= 965107913
              exact Brocard.berndt_galway_chunk_5367 n m (by omega) (by omega) h
          · -- n >= 965287769
            exact Brocard.berndt_galway_chunk_5368 n m (by omega) (by omega) h
        · -- n >= 965467625
          rcases Nat.lt_or_ge n 965827338 with hs4 | hs4
          · -- n < 965827338
            rcases Nat.lt_or_ge n 965647482 with hs5 | hs5
            · -- n < 965647482
              exact Brocard.berndt_galway_chunk_5369 n m (by omega) (by omega) h
            · -- n >= 965647482
              exact Brocard.berndt_galway_chunk_5370 n m (by omega) (by omega) h
          · -- n >= 965827338
            exact Brocard.berndt_galway_chunk_5371 n m (by omega) (by omega) h
      · -- n >= 966007194
        rcases Nat.lt_or_ge n 966546762 with hs3 | hs3
        · -- n < 966546762
          rcases Nat.lt_or_ge n 966366906 with hs4 | hs4
          · -- n < 966366906
            rcases Nat.lt_or_ge n 966187050 with hs5 | hs5
            · -- n < 966187050
              exact Brocard.berndt_galway_chunk_5372 n m (by omega) (by omega) h
            · -- n >= 966187050
              exact Brocard.berndt_galway_chunk_5373 n m (by omega) (by omega) h
          · -- n >= 966366906
            exact Brocard.berndt_galway_chunk_5374 n m (by omega) (by omega) h
        · -- n >= 966546762
          rcases Nat.lt_or_ge n 966726618 with hs4 | hs4
          · -- n < 966726618
            exact Brocard.berndt_galway_chunk_5375 n m (by omega) (by omega) h
          · -- n >= 966726618
            exact Brocard.berndt_galway_chunk_5376 n m (by omega) (by omega) h
