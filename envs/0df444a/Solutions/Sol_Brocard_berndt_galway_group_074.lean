-- Prove2me | solution 1 for Brocard.berndt_galway_group_074
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:44:38.147851+00:00
-- url     : https://prove2.me/submissions/79b401c4-8e1c-4c65-8d92-d7eaaa389c11

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_3384
import Theorems.Thm_Brocard_berndt_galway_chunk_3385
import Theorems.Thm_Brocard_berndt_galway_chunk_3386
import Theorems.Thm_Brocard_berndt_galway_chunk_3387
import Theorems.Thm_Brocard_berndt_galway_chunk_3388
import Theorems.Thm_Brocard_berndt_galway_chunk_3389
import Theorems.Thm_Brocard_berndt_galway_chunk_3390
import Theorems.Thm_Brocard_berndt_galway_chunk_3391
import Theorems.Thm_Brocard_berndt_galway_chunk_3392
import Theorems.Thm_Brocard_berndt_galway_chunk_3393
import Theorems.Thm_Brocard_berndt_galway_chunk_3394
import Theorems.Thm_Brocard_berndt_galway_chunk_3395
import Theorems.Thm_Brocard_berndt_galway_chunk_3396
import Theorems.Thm_Brocard_berndt_galway_chunk_3397
import Theorems.Thm_Brocard_berndt_galway_chunk_3398
import Theorems.Thm_Brocard_berndt_galway_chunk_3399
import Theorems.Thm_Brocard_berndt_galway_chunk_3400
import Theorems.Thm_Brocard_berndt_galway_chunk_3401
import Theorems.Thm_Brocard_berndt_galway_chunk_3402
import Theorems.Thm_Brocard_berndt_galway_chunk_3403
import Theorems.Thm_Brocard_berndt_galway_chunk_3404
import Theorems.Thm_Brocard_berndt_galway_chunk_3405
import Theorems.Thm_Brocard_berndt_galway_chunk_3406
import Theorems.Thm_Brocard_berndt_galway_chunk_3407
import Theorems.Thm_Brocard_berndt_galway_chunk_3408
import Theorems.Thm_Brocard_berndt_galway_chunk_3409
import Theorems.Thm_Brocard_berndt_galway_chunk_3410
import Theorems.Thm_Brocard_berndt_galway_chunk_3411
import Theorems.Thm_Brocard_berndt_galway_chunk_3412
import Theorems.Thm_Brocard_berndt_galway_chunk_3413
import Theorems.Thm_Brocard_berndt_galway_chunk_3414
import Theorems.Thm_Brocard_berndt_galway_chunk_3415
import Theorems.Thm_Brocard_berndt_galway_chunk_3416
import Theorems.Thm_Brocard_berndt_galway_chunk_3417
import Theorems.Thm_Brocard_berndt_galway_chunk_3418
import Theorems.Thm_Brocard_berndt_galway_chunk_3419
import Theorems.Thm_Brocard_berndt_galway_chunk_3420
import Theorems.Thm_Brocard_berndt_galway_chunk_3421
import Theorems.Thm_Brocard_berndt_galway_chunk_3422
import Theorems.Thm_Brocard_berndt_galway_chunk_3423
import Theorems.Thm_Brocard_berndt_galway_chunk_3424
import Theorems.Thm_Brocard_berndt_galway_chunk_3425
import Theorems.Thm_Brocard_berndt_galway_chunk_3426
import Theorems.Thm_Brocard_berndt_galway_chunk_3427
import Theorems.Thm_Brocard_berndt_galway_chunk_3428
import Theorems.Thm_Brocard_berndt_galway_chunk_3429
import Theorems.Thm_Brocard_berndt_galway_chunk_3430

theorem solution (n m : ℕ) (h1 : 608453237 ≤ n) (h2 : n < 616906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 612769784 with hs0 | hs0
  · -- n < 612769784
    rcases Nat.lt_or_ge n 610611510 with hs1 | hs1
    · -- n < 610611510
      rcases Nat.lt_or_ge n 609532374 with hs2 | hs2
      · -- n < 609532374
        rcases Nat.lt_or_ge n 608992805 with hs3 | hs3
        · -- n < 608992805
          rcases Nat.lt_or_ge n 608812949 with hs4 | hs4
          · -- n < 608812949
            rcases Nat.lt_or_ge n 608633093 with hs5 | hs5
            · -- n < 608633093
              exact Brocard.berndt_galway_chunk_3384 n m (by omega) (by omega) h
            · -- n >= 608633093
              exact Brocard.berndt_galway_chunk_3385 n m (by omega) (by omega) h
          · -- n >= 608812949
            exact Brocard.berndt_galway_chunk_3386 n m (by omega) (by omega) h
        · -- n >= 608992805
          rcases Nat.lt_or_ge n 609352517 with hs4 | hs4
          · -- n < 609352517
            rcases Nat.lt_or_ge n 609172661 with hs5 | hs5
            · -- n < 609172661
              exact Brocard.berndt_galway_chunk_3387 n m (by omega) (by omega) h
            · -- n >= 609172661
              exact Brocard.berndt_galway_chunk_3388 n m (by omega) (by omega) h
          · -- n >= 609352517
            exact Brocard.berndt_galway_chunk_3389 n m (by omega) (by omega) h
      · -- n >= 609532374
        rcases Nat.lt_or_ge n 610071942 with hs3 | hs3
        · -- n < 610071942
          rcases Nat.lt_or_ge n 609892086 with hs4 | hs4
          · -- n < 609892086
            rcases Nat.lt_or_ge n 609712230 with hs5 | hs5
            · -- n < 609712230
              exact Brocard.berndt_galway_chunk_3390 n m (by omega) (by omega) h
            · -- n >= 609712230
              exact Brocard.berndt_galway_chunk_3391 n m (by omega) (by omega) h
          · -- n >= 609892086
            exact Brocard.berndt_galway_chunk_3392 n m (by omega) (by omega) h
        · -- n >= 610071942
          rcases Nat.lt_or_ge n 610431654 with hs4 | hs4
          · -- n < 610431654
            rcases Nat.lt_or_ge n 610251798 with hs5 | hs5
            · -- n < 610251798
              exact Brocard.berndt_galway_chunk_3393 n m (by omega) (by omega) h
            · -- n >= 610251798
              exact Brocard.berndt_galway_chunk_3394 n m (by omega) (by omega) h
          · -- n >= 610431654
            exact Brocard.berndt_galway_chunk_3395 n m (by omega) (by omega) h
    · -- n >= 610611510
      rcases Nat.lt_or_ge n 611690647 with hs2 | hs2
      · -- n < 611690647
        rcases Nat.lt_or_ge n 611151079 with hs3 | hs3
        · -- n < 611151079
          rcases Nat.lt_or_ge n 610971223 with hs4 | hs4
          · -- n < 610971223
            rcases Nat.lt_or_ge n 610791366 with hs5 | hs5
            · -- n < 610791366
              exact Brocard.berndt_galway_chunk_3396 n m (by omega) (by omega) h
            · -- n >= 610791366
              exact Brocard.berndt_galway_chunk_3397 n m (by omega) (by omega) h
          · -- n >= 610971223
            exact Brocard.berndt_galway_chunk_3398 n m (by omega) (by omega) h
        · -- n >= 611151079
          rcases Nat.lt_or_ge n 611510791 with hs4 | hs4
          · -- n < 611510791
            rcases Nat.lt_or_ge n 611330935 with hs5 | hs5
            · -- n < 611330935
              exact Brocard.berndt_galway_chunk_3399 n m (by omega) (by omega) h
            · -- n >= 611330935
              exact Brocard.berndt_galway_chunk_3400 n m (by omega) (by omega) h
          · -- n >= 611510791
            exact Brocard.berndt_galway_chunk_3401 n m (by omega) (by omega) h
      · -- n >= 611690647
        rcases Nat.lt_or_ge n 612230215 with hs3 | hs3
        · -- n < 612230215
          rcases Nat.lt_or_ge n 612050359 with hs4 | hs4
          · -- n < 612050359
            rcases Nat.lt_or_ge n 611870503 with hs5 | hs5
            · -- n < 611870503
              exact Brocard.berndt_galway_chunk_3402 n m (by omega) (by omega) h
            · -- n >= 611870503
              exact Brocard.berndt_galway_chunk_3403 n m (by omega) (by omega) h
          · -- n >= 612050359
            exact Brocard.berndt_galway_chunk_3404 n m (by omega) (by omega) h
        · -- n >= 612230215
          rcases Nat.lt_or_ge n 612589928 with hs4 | hs4
          · -- n < 612589928
            rcases Nat.lt_or_ge n 612410071 with hs5 | hs5
            · -- n < 612410071
              exact Brocard.berndt_galway_chunk_3405 n m (by omega) (by omega) h
            · -- n >= 612410071
              exact Brocard.berndt_galway_chunk_3406 n m (by omega) (by omega) h
          · -- n >= 612589928
            exact Brocard.berndt_galway_chunk_3407 n m (by omega) (by omega) h
  · -- n >= 612769784
    rcases Nat.lt_or_ge n 614928057 with hs1 | hs1
    · -- n < 614928057
      rcases Nat.lt_or_ge n 613848920 with hs2 | hs2
      · -- n < 613848920
        rcases Nat.lt_or_ge n 613309352 with hs3 | hs3
        · -- n < 613309352
          rcases Nat.lt_or_ge n 613129496 with hs4 | hs4
          · -- n < 613129496
            rcases Nat.lt_or_ge n 612949640 with hs5 | hs5
            · -- n < 612949640
              exact Brocard.berndt_galway_chunk_3408 n m (by omega) (by omega) h
            · -- n >= 612949640
              exact Brocard.berndt_galway_chunk_3409 n m (by omega) (by omega) h
          · -- n >= 613129496
            exact Brocard.berndt_galway_chunk_3410 n m (by omega) (by omega) h
        · -- n >= 613309352
          rcases Nat.lt_or_ge n 613669064 with hs4 | hs4
          · -- n < 613669064
            rcases Nat.lt_or_ge n 613489208 with hs5 | hs5
            · -- n < 613489208
              exact Brocard.berndt_galway_chunk_3411 n m (by omega) (by omega) h
            · -- n >= 613489208
              exact Brocard.berndt_galway_chunk_3412 n m (by omega) (by omega) h
          · -- n >= 613669064
            exact Brocard.berndt_galway_chunk_3413 n m (by omega) (by omega) h
      · -- n >= 613848920
        rcases Nat.lt_or_ge n 614388489 with hs3 | hs3
        · -- n < 614388489
          rcases Nat.lt_or_ge n 614208633 with hs4 | hs4
          · -- n < 614208633
            rcases Nat.lt_or_ge n 614028776 with hs5 | hs5
            · -- n < 614028776
              exact Brocard.berndt_galway_chunk_3414 n m (by omega) (by omega) h
            · -- n >= 614028776
              exact Brocard.berndt_galway_chunk_3415 n m (by omega) (by omega) h
          · -- n >= 614208633
            exact Brocard.berndt_galway_chunk_3416 n m (by omega) (by omega) h
        · -- n >= 614388489
          rcases Nat.lt_or_ge n 614748201 with hs4 | hs4
          · -- n < 614748201
            rcases Nat.lt_or_ge n 614568345 with hs5 | hs5
            · -- n < 614568345
              exact Brocard.berndt_galway_chunk_3417 n m (by omega) (by omega) h
            · -- n >= 614568345
              exact Brocard.berndt_galway_chunk_3418 n m (by omega) (by omega) h
          · -- n >= 614748201
            exact Brocard.berndt_galway_chunk_3419 n m (by omega) (by omega) h
    · -- n >= 614928057
      rcases Nat.lt_or_ge n 616007194 with hs2 | hs2
      · -- n < 616007194
        rcases Nat.lt_or_ge n 615467625 with hs3 | hs3
        · -- n < 615467625
          rcases Nat.lt_or_ge n 615287769 with hs4 | hs4
          · -- n < 615287769
            rcases Nat.lt_or_ge n 615107913 with hs5 | hs5
            · -- n < 615107913
              exact Brocard.berndt_galway_chunk_3420 n m (by omega) (by omega) h
            · -- n >= 615107913
              exact Brocard.berndt_galway_chunk_3421 n m (by omega) (by omega) h
          · -- n >= 615287769
            exact Brocard.berndt_galway_chunk_3422 n m (by omega) (by omega) h
        · -- n >= 615467625
          rcases Nat.lt_or_ge n 615827338 with hs4 | hs4
          · -- n < 615827338
            rcases Nat.lt_or_ge n 615647482 with hs5 | hs5
            · -- n < 615647482
              exact Brocard.berndt_galway_chunk_3423 n m (by omega) (by omega) h
            · -- n >= 615647482
              exact Brocard.berndt_galway_chunk_3424 n m (by omega) (by omega) h
          · -- n >= 615827338
            exact Brocard.berndt_galway_chunk_3425 n m (by omega) (by omega) h
      · -- n >= 616007194
        rcases Nat.lt_or_ge n 616546762 with hs3 | hs3
        · -- n < 616546762
          rcases Nat.lt_or_ge n 616366906 with hs4 | hs4
          · -- n < 616366906
            rcases Nat.lt_or_ge n 616187050 with hs5 | hs5
            · -- n < 616187050
              exact Brocard.berndt_galway_chunk_3426 n m (by omega) (by omega) h
            · -- n >= 616187050
              exact Brocard.berndt_galway_chunk_3427 n m (by omega) (by omega) h
          · -- n >= 616366906
            exact Brocard.berndt_galway_chunk_3428 n m (by omega) (by omega) h
        · -- n >= 616546762
          rcases Nat.lt_or_ge n 616726618 with hs4 | hs4
          · -- n < 616726618
            exact Brocard.berndt_galway_chunk_3429 n m (by omega) (by omega) h
          · -- n >= 616726618
            exact Brocard.berndt_galway_chunk_3430 n m (by omega) (by omega) h
