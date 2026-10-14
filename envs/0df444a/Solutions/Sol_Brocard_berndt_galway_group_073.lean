-- Prove2me | solution 1 for Brocard.berndt_galway_group_073
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:40:50.932485+00:00
-- url     : https://prove2.me/submissions/c7ec42e6-8f8c-4962-8d19-436790e94d2d

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_3337
import Theorems.Thm_Brocard_berndt_galway_chunk_3338
import Theorems.Thm_Brocard_berndt_galway_chunk_3339
import Theorems.Thm_Brocard_berndt_galway_chunk_3340
import Theorems.Thm_Brocard_berndt_galway_chunk_3341
import Theorems.Thm_Brocard_berndt_galway_chunk_3342
import Theorems.Thm_Brocard_berndt_galway_chunk_3343
import Theorems.Thm_Brocard_berndt_galway_chunk_3344
import Theorems.Thm_Brocard_berndt_galway_chunk_3345
import Theorems.Thm_Brocard_berndt_galway_chunk_3346
import Theorems.Thm_Brocard_berndt_galway_chunk_3347
import Theorems.Thm_Brocard_berndt_galway_chunk_3348
import Theorems.Thm_Brocard_berndt_galway_chunk_3349
import Theorems.Thm_Brocard_berndt_galway_chunk_3350
import Theorems.Thm_Brocard_berndt_galway_chunk_3351
import Theorems.Thm_Brocard_berndt_galway_chunk_3352
import Theorems.Thm_Brocard_berndt_galway_chunk_3353
import Theorems.Thm_Brocard_berndt_galway_chunk_3354
import Theorems.Thm_Brocard_berndt_galway_chunk_3355
import Theorems.Thm_Brocard_berndt_galway_chunk_3356
import Theorems.Thm_Brocard_berndt_galway_chunk_3357
import Theorems.Thm_Brocard_berndt_galway_chunk_3358
import Theorems.Thm_Brocard_berndt_galway_chunk_3359
import Theorems.Thm_Brocard_berndt_galway_chunk_3360
import Theorems.Thm_Brocard_berndt_galway_chunk_3361
import Theorems.Thm_Brocard_berndt_galway_chunk_3362
import Theorems.Thm_Brocard_berndt_galway_chunk_3363
import Theorems.Thm_Brocard_berndt_galway_chunk_3364
import Theorems.Thm_Brocard_berndt_galway_chunk_3365
import Theorems.Thm_Brocard_berndt_galway_chunk_3366
import Theorems.Thm_Brocard_berndt_galway_chunk_3367
import Theorems.Thm_Brocard_berndt_galway_chunk_3368
import Theorems.Thm_Brocard_berndt_galway_chunk_3369
import Theorems.Thm_Brocard_berndt_galway_chunk_3370
import Theorems.Thm_Brocard_berndt_galway_chunk_3371
import Theorems.Thm_Brocard_berndt_galway_chunk_3372
import Theorems.Thm_Brocard_berndt_galway_chunk_3373
import Theorems.Thm_Brocard_berndt_galway_chunk_3374
import Theorems.Thm_Brocard_berndt_galway_chunk_3375
import Theorems.Thm_Brocard_berndt_galway_chunk_3376
import Theorems.Thm_Brocard_berndt_galway_chunk_3377
import Theorems.Thm_Brocard_berndt_galway_chunk_3378
import Theorems.Thm_Brocard_berndt_galway_chunk_3379
import Theorems.Thm_Brocard_berndt_galway_chunk_3380
import Theorems.Thm_Brocard_berndt_galway_chunk_3381
import Theorems.Thm_Brocard_berndt_galway_chunk_3382
import Theorems.Thm_Brocard_berndt_galway_chunk_3383

theorem solution (n m : ℕ) (h1 : 600000000 ≤ n) (h2 : n < 608453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 604316546 with hs0 | hs0
  · -- n < 604316546
    rcases Nat.lt_or_ge n 602158273 with hs1 | hs1
    · -- n < 602158273
      rcases Nat.lt_or_ge n 601079136 with hs2 | hs2
      · -- n < 601079136
        rcases Nat.lt_or_ge n 600539568 with hs3 | hs3
        · -- n < 600539568
          rcases Nat.lt_or_ge n 600359712 with hs4 | hs4
          · -- n < 600359712
            rcases Nat.lt_or_ge n 600179856 with hs5 | hs5
            · -- n < 600179856
              exact Brocard.berndt_galway_chunk_3337 n m (by omega) (by omega) h
            · -- n >= 600179856
              exact Brocard.berndt_galway_chunk_3338 n m (by omega) (by omega) h
          · -- n >= 600359712
            exact Brocard.berndt_galway_chunk_3339 n m (by omega) (by omega) h
        · -- n >= 600539568
          rcases Nat.lt_or_ge n 600899280 with hs4 | hs4
          · -- n < 600899280
            rcases Nat.lt_or_ge n 600719424 with hs5 | hs5
            · -- n < 600719424
              exact Brocard.berndt_galway_chunk_3340 n m (by omega) (by omega) h
            · -- n >= 600719424
              exact Brocard.berndt_galway_chunk_3341 n m (by omega) (by omega) h
          · -- n >= 600899280
            exact Brocard.berndt_galway_chunk_3342 n m (by omega) (by omega) h
      · -- n >= 601079136
        rcases Nat.lt_or_ge n 601618705 with hs3 | hs3
        · -- n < 601618705
          rcases Nat.lt_or_ge n 601438848 with hs4 | hs4
          · -- n < 601438848
            rcases Nat.lt_or_ge n 601258992 with hs5 | hs5
            · -- n < 601258992
              exact Brocard.berndt_galway_chunk_3343 n m (by omega) (by omega) h
            · -- n >= 601258992
              exact Brocard.berndt_galway_chunk_3344 n m (by omega) (by omega) h
          · -- n >= 601438848
            exact Brocard.berndt_galway_chunk_3345 n m (by omega) (by omega) h
        · -- n >= 601618705
          rcases Nat.lt_or_ge n 601978417 with hs4 | hs4
          · -- n < 601978417
            rcases Nat.lt_or_ge n 601798561 with hs5 | hs5
            · -- n < 601798561
              exact Brocard.berndt_galway_chunk_3346 n m (by omega) (by omega) h
            · -- n >= 601798561
              exact Brocard.berndt_galway_chunk_3347 n m (by omega) (by omega) h
          · -- n >= 601978417
            exact Brocard.berndt_galway_chunk_3348 n m (by omega) (by omega) h
    · -- n >= 602158273
      rcases Nat.lt_or_ge n 603237410 with hs2 | hs2
      · -- n < 603237410
        rcases Nat.lt_or_ge n 602697841 with hs3 | hs3
        · -- n < 602697841
          rcases Nat.lt_or_ge n 602517985 with hs4 | hs4
          · -- n < 602517985
            rcases Nat.lt_or_ge n 602338129 with hs5 | hs5
            · -- n < 602338129
              exact Brocard.berndt_galway_chunk_3349 n m (by omega) (by omega) h
            · -- n >= 602338129
              exact Brocard.berndt_galway_chunk_3350 n m (by omega) (by omega) h
          · -- n >= 602517985
            exact Brocard.berndt_galway_chunk_3351 n m (by omega) (by omega) h
        · -- n >= 602697841
          rcases Nat.lt_or_ge n 603057553 with hs4 | hs4
          · -- n < 603057553
            rcases Nat.lt_or_ge n 602877697 with hs5 | hs5
            · -- n < 602877697
              exact Brocard.berndt_galway_chunk_3352 n m (by omega) (by omega) h
            · -- n >= 602877697
              exact Brocard.berndt_galway_chunk_3353 n m (by omega) (by omega) h
          · -- n >= 603057553
            exact Brocard.berndt_galway_chunk_3354 n m (by omega) (by omega) h
      · -- n >= 603237410
        rcases Nat.lt_or_ge n 603776978 with hs3 | hs3
        · -- n < 603776978
          rcases Nat.lt_or_ge n 603597122 with hs4 | hs4
          · -- n < 603597122
            rcases Nat.lt_or_ge n 603417266 with hs5 | hs5
            · -- n < 603417266
              exact Brocard.berndt_galway_chunk_3355 n m (by omega) (by omega) h
            · -- n >= 603417266
              exact Brocard.berndt_galway_chunk_3356 n m (by omega) (by omega) h
          · -- n >= 603597122
            exact Brocard.berndt_galway_chunk_3357 n m (by omega) (by omega) h
        · -- n >= 603776978
          rcases Nat.lt_or_ge n 604136690 with hs4 | hs4
          · -- n < 604136690
            rcases Nat.lt_or_ge n 603956834 with hs5 | hs5
            · -- n < 603956834
              exact Brocard.berndt_galway_chunk_3358 n m (by omega) (by omega) h
            · -- n >= 603956834
              exact Brocard.berndt_galway_chunk_3359 n m (by omega) (by omega) h
          · -- n >= 604136690
            exact Brocard.berndt_galway_chunk_3360 n m (by omega) (by omega) h
  · -- n >= 604316546
    rcases Nat.lt_or_ge n 606474820 with hs1 | hs1
    · -- n < 606474820
      rcases Nat.lt_or_ge n 605395683 with hs2 | hs2
      · -- n < 605395683
        rcases Nat.lt_or_ge n 604856115 with hs3 | hs3
        · -- n < 604856115
          rcases Nat.lt_or_ge n 604676258 with hs4 | hs4
          · -- n < 604676258
            rcases Nat.lt_or_ge n 604496402 with hs5 | hs5
            · -- n < 604496402
              exact Brocard.berndt_galway_chunk_3361 n m (by omega) (by omega) h
            · -- n >= 604496402
              exact Brocard.berndt_galway_chunk_3362 n m (by omega) (by omega) h
          · -- n >= 604676258
            exact Brocard.berndt_galway_chunk_3363 n m (by omega) (by omega) h
        · -- n >= 604856115
          rcases Nat.lt_or_ge n 605215827 with hs4 | hs4
          · -- n < 605215827
            rcases Nat.lt_or_ge n 605035971 with hs5 | hs5
            · -- n < 605035971
              exact Brocard.berndt_galway_chunk_3364 n m (by omega) (by omega) h
            · -- n >= 605035971
              exact Brocard.berndt_galway_chunk_3365 n m (by omega) (by omega) h
          · -- n >= 605215827
            exact Brocard.berndt_galway_chunk_3366 n m (by omega) (by omega) h
      · -- n >= 605395683
        rcases Nat.lt_or_ge n 605935251 with hs3 | hs3
        · -- n < 605935251
          rcases Nat.lt_or_ge n 605755395 with hs4 | hs4
          · -- n < 605755395
            rcases Nat.lt_or_ge n 605575539 with hs5 | hs5
            · -- n < 605575539
              exact Brocard.berndt_galway_chunk_3367 n m (by omega) (by omega) h
            · -- n >= 605575539
              exact Brocard.berndt_galway_chunk_3368 n m (by omega) (by omega) h
          · -- n >= 605755395
            exact Brocard.berndt_galway_chunk_3369 n m (by omega) (by omega) h
        · -- n >= 605935251
          rcases Nat.lt_or_ge n 606294964 with hs4 | hs4
          · -- n < 606294964
            rcases Nat.lt_or_ge n 606115107 with hs5 | hs5
            · -- n < 606115107
              exact Brocard.berndt_galway_chunk_3370 n m (by omega) (by omega) h
            · -- n >= 606115107
              exact Brocard.berndt_galway_chunk_3371 n m (by omega) (by omega) h
          · -- n >= 606294964
            exact Brocard.berndt_galway_chunk_3372 n m (by omega) (by omega) h
    · -- n >= 606474820
      rcases Nat.lt_or_ge n 607553956 with hs2 | hs2
      · -- n < 607553956
        rcases Nat.lt_or_ge n 607014388 with hs3 | hs3
        · -- n < 607014388
          rcases Nat.lt_or_ge n 606834532 with hs4 | hs4
          · -- n < 606834532
            rcases Nat.lt_or_ge n 606654676 with hs5 | hs5
            · -- n < 606654676
              exact Brocard.berndt_galway_chunk_3373 n m (by omega) (by omega) h
            · -- n >= 606654676
              exact Brocard.berndt_galway_chunk_3374 n m (by omega) (by omega) h
          · -- n >= 606834532
            exact Brocard.berndt_galway_chunk_3375 n m (by omega) (by omega) h
        · -- n >= 607014388
          rcases Nat.lt_or_ge n 607374100 with hs4 | hs4
          · -- n < 607374100
            rcases Nat.lt_or_ge n 607194244 with hs5 | hs5
            · -- n < 607194244
              exact Brocard.berndt_galway_chunk_3376 n m (by omega) (by omega) h
            · -- n >= 607194244
              exact Brocard.berndt_galway_chunk_3377 n m (by omega) (by omega) h
          · -- n >= 607374100
            exact Brocard.berndt_galway_chunk_3378 n m (by omega) (by omega) h
      · -- n >= 607553956
        rcases Nat.lt_or_ge n 608093525 with hs3 | hs3
        · -- n < 608093525
          rcases Nat.lt_or_ge n 607913669 with hs4 | hs4
          · -- n < 607913669
            rcases Nat.lt_or_ge n 607733812 with hs5 | hs5
            · -- n < 607733812
              exact Brocard.berndt_galway_chunk_3379 n m (by omega) (by omega) h
            · -- n >= 607733812
              exact Brocard.berndt_galway_chunk_3380 n m (by omega) (by omega) h
          · -- n >= 607913669
            exact Brocard.berndt_galway_chunk_3381 n m (by omega) (by omega) h
        · -- n >= 608093525
          rcases Nat.lt_or_ge n 608273381 with hs4 | hs4
          · -- n < 608273381
            exact Brocard.berndt_galway_chunk_3382 n m (by omega) (by omega) h
          · -- n >= 608273381
            exact Brocard.berndt_galway_chunk_3383 n m (by omega) (by omega) h
