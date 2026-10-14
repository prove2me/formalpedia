-- Prove2me | solution 1 for Brocard.berndt_galway_group_052
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:45:10.531981+00:00
-- url     : https://prove2.me/submissions/1df0e538-7cc0-470c-a882-e6d5923ce086

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_2366
import Theorems.Thm_Brocard_berndt_galway_chunk_2367
import Theorems.Thm_Brocard_berndt_galway_chunk_2368
import Theorems.Thm_Brocard_berndt_galway_chunk_2369
import Theorems.Thm_Brocard_berndt_galway_chunk_2370
import Theorems.Thm_Brocard_berndt_galway_chunk_2371
import Theorems.Thm_Brocard_berndt_galway_chunk_2372
import Theorems.Thm_Brocard_berndt_galway_chunk_2373
import Theorems.Thm_Brocard_berndt_galway_chunk_2374
import Theorems.Thm_Brocard_berndt_galway_chunk_2375
import Theorems.Thm_Brocard_berndt_galway_chunk_2376
import Theorems.Thm_Brocard_berndt_galway_chunk_2377
import Theorems.Thm_Brocard_berndt_galway_chunk_2378
import Theorems.Thm_Brocard_berndt_galway_chunk_2379
import Theorems.Thm_Brocard_berndt_galway_chunk_2380
import Theorems.Thm_Brocard_berndt_galway_chunk_2381
import Theorems.Thm_Brocard_berndt_galway_chunk_2382
import Theorems.Thm_Brocard_berndt_galway_chunk_2383
import Theorems.Thm_Brocard_berndt_galway_chunk_2384
import Theorems.Thm_Brocard_berndt_galway_chunk_2385
import Theorems.Thm_Brocard_berndt_galway_chunk_2386
import Theorems.Thm_Brocard_berndt_galway_chunk_2387
import Theorems.Thm_Brocard_berndt_galway_chunk_2388
import Theorems.Thm_Brocard_berndt_galway_chunk_2389
import Theorems.Thm_Brocard_berndt_galway_chunk_2390
import Theorems.Thm_Brocard_berndt_galway_chunk_2391
import Theorems.Thm_Brocard_berndt_galway_chunk_2392
import Theorems.Thm_Brocard_berndt_galway_chunk_2393
import Theorems.Thm_Brocard_berndt_galway_chunk_2394
import Theorems.Thm_Brocard_berndt_galway_chunk_2395
import Theorems.Thm_Brocard_berndt_galway_chunk_2396
import Theorems.Thm_Brocard_berndt_galway_chunk_2397
import Theorems.Thm_Brocard_berndt_galway_chunk_2398
import Theorems.Thm_Brocard_berndt_galway_chunk_2399
import Theorems.Thm_Brocard_berndt_galway_chunk_2400
import Theorems.Thm_Brocard_berndt_galway_chunk_2401
import Theorems.Thm_Brocard_berndt_galway_chunk_2402
import Theorems.Thm_Brocard_berndt_galway_chunk_2403
import Theorems.Thm_Brocard_berndt_galway_chunk_2404
import Theorems.Thm_Brocard_berndt_galway_chunk_2405
import Theorems.Thm_Brocard_berndt_galway_chunk_2406
import Theorems.Thm_Brocard_berndt_galway_chunk_2407
import Theorems.Thm_Brocard_berndt_galway_chunk_2408
import Theorems.Thm_Brocard_berndt_galway_chunk_2409
import Theorems.Thm_Brocard_berndt_galway_chunk_2410
import Theorems.Thm_Brocard_berndt_galway_chunk_2411
import Theorems.Thm_Brocard_berndt_galway_chunk_2412

theorem solution (n m : ℕ) (h1 : 425359712 ≤ n) (h2 : n < 433812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 429676258 with hs0 | hs0
  · -- n < 429676258
    rcases Nat.lt_or_ge n 427517985 with hs1 | hs1
    · -- n < 427517985
      rcases Nat.lt_or_ge n 426438848 with hs2 | hs2
      · -- n < 426438848
        rcases Nat.lt_or_ge n 425899280 with hs3 | hs3
        · -- n < 425899280
          rcases Nat.lt_or_ge n 425719424 with hs4 | hs4
          · -- n < 425719424
            rcases Nat.lt_or_ge n 425539568 with hs5 | hs5
            · -- n < 425539568
              exact Brocard.berndt_galway_chunk_2366 n m (by omega) (by omega) h
            · -- n >= 425539568
              exact Brocard.berndt_galway_chunk_2367 n m (by omega) (by omega) h
          · -- n >= 425719424
            exact Brocard.berndt_galway_chunk_2368 n m (by omega) (by omega) h
        · -- n >= 425899280
          rcases Nat.lt_or_ge n 426258992 with hs4 | hs4
          · -- n < 426258992
            rcases Nat.lt_or_ge n 426079136 with hs5 | hs5
            · -- n < 426079136
              exact Brocard.berndt_galway_chunk_2369 n m (by omega) (by omega) h
            · -- n >= 426079136
              exact Brocard.berndt_galway_chunk_2370 n m (by omega) (by omega) h
          · -- n >= 426258992
            exact Brocard.berndt_galway_chunk_2371 n m (by omega) (by omega) h
      · -- n >= 426438848
        rcases Nat.lt_or_ge n 426978417 with hs3 | hs3
        · -- n < 426978417
          rcases Nat.lt_or_ge n 426798561 with hs4 | hs4
          · -- n < 426798561
            rcases Nat.lt_or_ge n 426618705 with hs5 | hs5
            · -- n < 426618705
              exact Brocard.berndt_galway_chunk_2372 n m (by omega) (by omega) h
            · -- n >= 426618705
              exact Brocard.berndt_galway_chunk_2373 n m (by omega) (by omega) h
          · -- n >= 426798561
            exact Brocard.berndt_galway_chunk_2374 n m (by omega) (by omega) h
        · -- n >= 426978417
          rcases Nat.lt_or_ge n 427338129 with hs4 | hs4
          · -- n < 427338129
            rcases Nat.lt_or_ge n 427158273 with hs5 | hs5
            · -- n < 427158273
              exact Brocard.berndt_galway_chunk_2375 n m (by omega) (by omega) h
            · -- n >= 427158273
              exact Brocard.berndt_galway_chunk_2376 n m (by omega) (by omega) h
          · -- n >= 427338129
            exact Brocard.berndt_galway_chunk_2377 n m (by omega) (by omega) h
    · -- n >= 427517985
      rcases Nat.lt_or_ge n 428597122 with hs2 | hs2
      · -- n < 428597122
        rcases Nat.lt_or_ge n 428057553 with hs3 | hs3
        · -- n < 428057553
          rcases Nat.lt_or_ge n 427877697 with hs4 | hs4
          · -- n < 427877697
            rcases Nat.lt_or_ge n 427697841 with hs5 | hs5
            · -- n < 427697841
              exact Brocard.berndt_galway_chunk_2378 n m (by omega) (by omega) h
            · -- n >= 427697841
              exact Brocard.berndt_galway_chunk_2379 n m (by omega) (by omega) h
          · -- n >= 427877697
            exact Brocard.berndt_galway_chunk_2380 n m (by omega) (by omega) h
        · -- n >= 428057553
          rcases Nat.lt_or_ge n 428417266 with hs4 | hs4
          · -- n < 428417266
            rcases Nat.lt_or_ge n 428237410 with hs5 | hs5
            · -- n < 428237410
              exact Brocard.berndt_galway_chunk_2381 n m (by omega) (by omega) h
            · -- n >= 428237410
              exact Brocard.berndt_galway_chunk_2382 n m (by omega) (by omega) h
          · -- n >= 428417266
            exact Brocard.berndt_galway_chunk_2383 n m (by omega) (by omega) h
      · -- n >= 428597122
        rcases Nat.lt_or_ge n 429136690 with hs3 | hs3
        · -- n < 429136690
          rcases Nat.lt_or_ge n 428956834 with hs4 | hs4
          · -- n < 428956834
            rcases Nat.lt_or_ge n 428776978 with hs5 | hs5
            · -- n < 428776978
              exact Brocard.berndt_galway_chunk_2384 n m (by omega) (by omega) h
            · -- n >= 428776978
              exact Brocard.berndt_galway_chunk_2385 n m (by omega) (by omega) h
          · -- n >= 428956834
            exact Brocard.berndt_galway_chunk_2386 n m (by omega) (by omega) h
        · -- n >= 429136690
          rcases Nat.lt_or_ge n 429496402 with hs4 | hs4
          · -- n < 429496402
            rcases Nat.lt_or_ge n 429316546 with hs5 | hs5
            · -- n < 429316546
              exact Brocard.berndt_galway_chunk_2387 n m (by omega) (by omega) h
            · -- n >= 429316546
              exact Brocard.berndt_galway_chunk_2388 n m (by omega) (by omega) h
          · -- n >= 429496402
            exact Brocard.berndt_galway_chunk_2389 n m (by omega) (by omega) h
  · -- n >= 429676258
    rcases Nat.lt_or_ge n 431834532 with hs1 | hs1
    · -- n < 431834532
      rcases Nat.lt_or_ge n 430755395 with hs2 | hs2
      · -- n < 430755395
        rcases Nat.lt_or_ge n 430215827 with hs3 | hs3
        · -- n < 430215827
          rcases Nat.lt_or_ge n 430035971 with hs4 | hs4
          · -- n < 430035971
            rcases Nat.lt_or_ge n 429856115 with hs5 | hs5
            · -- n < 429856115
              exact Brocard.berndt_galway_chunk_2390 n m (by omega) (by omega) h
            · -- n >= 429856115
              exact Brocard.berndt_galway_chunk_2391 n m (by omega) (by omega) h
          · -- n >= 430035971
            exact Brocard.berndt_galway_chunk_2392 n m (by omega) (by omega) h
        · -- n >= 430215827
          rcases Nat.lt_or_ge n 430575539 with hs4 | hs4
          · -- n < 430575539
            rcases Nat.lt_or_ge n 430395683 with hs5 | hs5
            · -- n < 430395683
              exact Brocard.berndt_galway_chunk_2393 n m (by omega) (by omega) h
            · -- n >= 430395683
              exact Brocard.berndt_galway_chunk_2394 n m (by omega) (by omega) h
          · -- n >= 430575539
            exact Brocard.berndt_galway_chunk_2395 n m (by omega) (by omega) h
      · -- n >= 430755395
        rcases Nat.lt_or_ge n 431294964 with hs3 | hs3
        · -- n < 431294964
          rcases Nat.lt_or_ge n 431115107 with hs4 | hs4
          · -- n < 431115107
            rcases Nat.lt_or_ge n 430935251 with hs5 | hs5
            · -- n < 430935251
              exact Brocard.berndt_galway_chunk_2396 n m (by omega) (by omega) h
            · -- n >= 430935251
              exact Brocard.berndt_galway_chunk_2397 n m (by omega) (by omega) h
          · -- n >= 431115107
            exact Brocard.berndt_galway_chunk_2398 n m (by omega) (by omega) h
        · -- n >= 431294964
          rcases Nat.lt_or_ge n 431654676 with hs4 | hs4
          · -- n < 431654676
            rcases Nat.lt_or_ge n 431474820 with hs5 | hs5
            · -- n < 431474820
              exact Brocard.berndt_galway_chunk_2399 n m (by omega) (by omega) h
            · -- n >= 431474820
              exact Brocard.berndt_galway_chunk_2400 n m (by omega) (by omega) h
          · -- n >= 431654676
            exact Brocard.berndt_galway_chunk_2401 n m (by omega) (by omega) h
    · -- n >= 431834532
      rcases Nat.lt_or_ge n 432913669 with hs2 | hs2
      · -- n < 432913669
        rcases Nat.lt_or_ge n 432374100 with hs3 | hs3
        · -- n < 432374100
          rcases Nat.lt_or_ge n 432194244 with hs4 | hs4
          · -- n < 432194244
            rcases Nat.lt_or_ge n 432014388 with hs5 | hs5
            · -- n < 432014388
              exact Brocard.berndt_galway_chunk_2402 n m (by omega) (by omega) h
            · -- n >= 432014388
              exact Brocard.berndt_galway_chunk_2403 n m (by omega) (by omega) h
          · -- n >= 432194244
            exact Brocard.berndt_galway_chunk_2404 n m (by omega) (by omega) h
        · -- n >= 432374100
          rcases Nat.lt_or_ge n 432733812 with hs4 | hs4
          · -- n < 432733812
            rcases Nat.lt_or_ge n 432553956 with hs5 | hs5
            · -- n < 432553956
              exact Brocard.berndt_galway_chunk_2405 n m (by omega) (by omega) h
            · -- n >= 432553956
              exact Brocard.berndt_galway_chunk_2406 n m (by omega) (by omega) h
          · -- n >= 432733812
            exact Brocard.berndt_galway_chunk_2407 n m (by omega) (by omega) h
      · -- n >= 432913669
        rcases Nat.lt_or_ge n 433453237 with hs3 | hs3
        · -- n < 433453237
          rcases Nat.lt_or_ge n 433273381 with hs4 | hs4
          · -- n < 433273381
            rcases Nat.lt_or_ge n 433093525 with hs5 | hs5
            · -- n < 433093525
              exact Brocard.berndt_galway_chunk_2408 n m (by omega) (by omega) h
            · -- n >= 433093525
              exact Brocard.berndt_galway_chunk_2409 n m (by omega) (by omega) h
          · -- n >= 433273381
            exact Brocard.berndt_galway_chunk_2410 n m (by omega) (by omega) h
        · -- n >= 433453237
          rcases Nat.lt_or_ge n 433633093 with hs4 | hs4
          · -- n < 433633093
            exact Brocard.berndt_galway_chunk_2411 n m (by omega) (by omega) h
          · -- n >= 433633093
            exact Brocard.berndt_galway_chunk_2412 n m (by omega) (by omega) h
