-- Prove2me | solution 1 for Brocard.berndt_galway_group_053
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:54:09.102795+00:00
-- url     : https://prove2.me/submissions/191814f9-5c14-4fbd-a735-a04b016c1b2f

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_2413
import Theorems.Thm_Brocard_berndt_galway_chunk_2414
import Theorems.Thm_Brocard_berndt_galway_chunk_2415
import Theorems.Thm_Brocard_berndt_galway_chunk_2416
import Theorems.Thm_Brocard_berndt_galway_chunk_2417
import Theorems.Thm_Brocard_berndt_galway_chunk_2418
import Theorems.Thm_Brocard_berndt_galway_chunk_2419
import Theorems.Thm_Brocard_berndt_galway_chunk_2420
import Theorems.Thm_Brocard_berndt_galway_chunk_2421
import Theorems.Thm_Brocard_berndt_galway_chunk_2422
import Theorems.Thm_Brocard_berndt_galway_chunk_2423
import Theorems.Thm_Brocard_berndt_galway_chunk_2424
import Theorems.Thm_Brocard_berndt_galway_chunk_2425
import Theorems.Thm_Brocard_berndt_galway_chunk_2426
import Theorems.Thm_Brocard_berndt_galway_chunk_2427
import Theorems.Thm_Brocard_berndt_galway_chunk_2428
import Theorems.Thm_Brocard_berndt_galway_chunk_2429
import Theorems.Thm_Brocard_berndt_galway_chunk_2430
import Theorems.Thm_Brocard_berndt_galway_chunk_2431
import Theorems.Thm_Brocard_berndt_galway_chunk_2432
import Theorems.Thm_Brocard_berndt_galway_chunk_2433
import Theorems.Thm_Brocard_berndt_galway_chunk_2434
import Theorems.Thm_Brocard_berndt_galway_chunk_2435
import Theorems.Thm_Brocard_berndt_galway_chunk_2436
import Theorems.Thm_Brocard_berndt_galway_chunk_2437
import Theorems.Thm_Brocard_berndt_galway_chunk_2438
import Theorems.Thm_Brocard_berndt_galway_chunk_2439
import Theorems.Thm_Brocard_berndt_galway_chunk_2440
import Theorems.Thm_Brocard_berndt_galway_chunk_2441
import Theorems.Thm_Brocard_berndt_galway_chunk_2442
import Theorems.Thm_Brocard_berndt_galway_chunk_2443
import Theorems.Thm_Brocard_berndt_galway_chunk_2444
import Theorems.Thm_Brocard_berndt_galway_chunk_2445
import Theorems.Thm_Brocard_berndt_galway_chunk_2446
import Theorems.Thm_Brocard_berndt_galway_chunk_2447
import Theorems.Thm_Brocard_berndt_galway_chunk_2448
import Theorems.Thm_Brocard_berndt_galway_chunk_2449
import Theorems.Thm_Brocard_berndt_galway_chunk_2450
import Theorems.Thm_Brocard_berndt_galway_chunk_2451
import Theorems.Thm_Brocard_berndt_galway_chunk_2452
import Theorems.Thm_Brocard_berndt_galway_chunk_2453
import Theorems.Thm_Brocard_berndt_galway_chunk_2454
import Theorems.Thm_Brocard_berndt_galway_chunk_2455
import Theorems.Thm_Brocard_berndt_galway_chunk_2456
import Theorems.Thm_Brocard_berndt_galway_chunk_2457
import Theorems.Thm_Brocard_berndt_galway_chunk_2458

theorem solution (n m : ℕ) (h1 : 433812949 ≤ n) (h2 : n < 442086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 437949640 with hs0 | hs0
  · -- n < 437949640
    rcases Nat.lt_or_ge n 435971223 with hs1 | hs1
    · -- n < 435971223
      rcases Nat.lt_or_ge n 434892086 with hs2 | hs2
      · -- n < 434892086
        rcases Nat.lt_or_ge n 434352517 with hs3 | hs3
        · -- n < 434352517
          rcases Nat.lt_or_ge n 434172661 with hs4 | hs4
          · -- n < 434172661
            rcases Nat.lt_or_ge n 433992805 with hs5 | hs5
            · -- n < 433992805
              exact Brocard.berndt_galway_chunk_2413 n m (by omega) (by omega) h
            · -- n >= 433992805
              exact Brocard.berndt_galway_chunk_2414 n m (by omega) (by omega) h
          · -- n >= 434172661
            exact Brocard.berndt_galway_chunk_2415 n m (by omega) (by omega) h
        · -- n >= 434352517
          rcases Nat.lt_or_ge n 434712230 with hs4 | hs4
          · -- n < 434712230
            rcases Nat.lt_or_ge n 434532374 with hs5 | hs5
            · -- n < 434532374
              exact Brocard.berndt_galway_chunk_2416 n m (by omega) (by omega) h
            · -- n >= 434532374
              exact Brocard.berndt_galway_chunk_2417 n m (by omega) (by omega) h
          · -- n >= 434712230
            exact Brocard.berndt_galway_chunk_2418 n m (by omega) (by omega) h
      · -- n >= 434892086
        rcases Nat.lt_or_ge n 435431654 with hs3 | hs3
        · -- n < 435431654
          rcases Nat.lt_or_ge n 435251798 with hs4 | hs4
          · -- n < 435251798
            rcases Nat.lt_or_ge n 435071942 with hs5 | hs5
            · -- n < 435071942
              exact Brocard.berndt_galway_chunk_2419 n m (by omega) (by omega) h
            · -- n >= 435071942
              exact Brocard.berndt_galway_chunk_2420 n m (by omega) (by omega) h
          · -- n >= 435251798
            exact Brocard.berndt_galway_chunk_2421 n m (by omega) (by omega) h
        · -- n >= 435431654
          rcases Nat.lt_or_ge n 435791366 with hs4 | hs4
          · -- n < 435791366
            rcases Nat.lt_or_ge n 435611510 with hs5 | hs5
            · -- n < 435611510
              exact Brocard.berndt_galway_chunk_2422 n m (by omega) (by omega) h
            · -- n >= 435611510
              exact Brocard.berndt_galway_chunk_2423 n m (by omega) (by omega) h
          · -- n >= 435791366
            exact Brocard.berndt_galway_chunk_2424 n m (by omega) (by omega) h
    · -- n >= 435971223
      rcases Nat.lt_or_ge n 437050359 with hs2 | hs2
      · -- n < 437050359
        rcases Nat.lt_or_ge n 436510791 with hs3 | hs3
        · -- n < 436510791
          rcases Nat.lt_or_ge n 436330935 with hs4 | hs4
          · -- n < 436330935
            rcases Nat.lt_or_ge n 436151079 with hs5 | hs5
            · -- n < 436151079
              exact Brocard.berndt_galway_chunk_2425 n m (by omega) (by omega) h
            · -- n >= 436151079
              exact Brocard.berndt_galway_chunk_2426 n m (by omega) (by omega) h
          · -- n >= 436330935
            exact Brocard.berndt_galway_chunk_2427 n m (by omega) (by omega) h
        · -- n >= 436510791
          rcases Nat.lt_or_ge n 436870503 with hs4 | hs4
          · -- n < 436870503
            rcases Nat.lt_or_ge n 436690647 with hs5 | hs5
            · -- n < 436690647
              exact Brocard.berndt_galway_chunk_2428 n m (by omega) (by omega) h
            · -- n >= 436690647
              exact Brocard.berndt_galway_chunk_2429 n m (by omega) (by omega) h
          · -- n >= 436870503
            exact Brocard.berndt_galway_chunk_2430 n m (by omega) (by omega) h
      · -- n >= 437050359
        rcases Nat.lt_or_ge n 437589928 with hs3 | hs3
        · -- n < 437589928
          rcases Nat.lt_or_ge n 437410071 with hs4 | hs4
          · -- n < 437410071
            rcases Nat.lt_or_ge n 437230215 with hs5 | hs5
            · -- n < 437230215
              exact Brocard.berndt_galway_chunk_2431 n m (by omega) (by omega) h
            · -- n >= 437230215
              exact Brocard.berndt_galway_chunk_2432 n m (by omega) (by omega) h
          · -- n >= 437410071
            exact Brocard.berndt_galway_chunk_2433 n m (by omega) (by omega) h
        · -- n >= 437589928
          rcases Nat.lt_or_ge n 437769784 with hs4 | hs4
          · -- n < 437769784
            exact Brocard.berndt_galway_chunk_2434 n m (by omega) (by omega) h
          · -- n >= 437769784
            exact Brocard.berndt_galway_chunk_2435 n m (by omega) (by omega) h
  · -- n >= 437949640
    rcases Nat.lt_or_ge n 440107913 with hs1 | hs1
    · -- n < 440107913
      rcases Nat.lt_or_ge n 439028776 with hs2 | hs2
      · -- n < 439028776
        rcases Nat.lt_or_ge n 438489208 with hs3 | hs3
        · -- n < 438489208
          rcases Nat.lt_or_ge n 438309352 with hs4 | hs4
          · -- n < 438309352
            rcases Nat.lt_or_ge n 438129496 with hs5 | hs5
            · -- n < 438129496
              exact Brocard.berndt_galway_chunk_2436 n m (by omega) (by omega) h
            · -- n >= 438129496
              exact Brocard.berndt_galway_chunk_2437 n m (by omega) (by omega) h
          · -- n >= 438309352
            exact Brocard.berndt_galway_chunk_2438 n m (by omega) (by omega) h
        · -- n >= 438489208
          rcases Nat.lt_or_ge n 438848920 with hs4 | hs4
          · -- n < 438848920
            rcases Nat.lt_or_ge n 438669064 with hs5 | hs5
            · -- n < 438669064
              exact Brocard.berndt_galway_chunk_2439 n m (by omega) (by omega) h
            · -- n >= 438669064
              exact Brocard.berndt_galway_chunk_2440 n m (by omega) (by omega) h
          · -- n >= 438848920
            exact Brocard.berndt_galway_chunk_2441 n m (by omega) (by omega) h
      · -- n >= 439028776
        rcases Nat.lt_or_ge n 439568345 with hs3 | hs3
        · -- n < 439568345
          rcases Nat.lt_or_ge n 439388489 with hs4 | hs4
          · -- n < 439388489
            rcases Nat.lt_or_ge n 439208633 with hs5 | hs5
            · -- n < 439208633
              exact Brocard.berndt_galway_chunk_2442 n m (by omega) (by omega) h
            · -- n >= 439208633
              exact Brocard.berndt_galway_chunk_2443 n m (by omega) (by omega) h
          · -- n >= 439388489
            exact Brocard.berndt_galway_chunk_2444 n m (by omega) (by omega) h
        · -- n >= 439568345
          rcases Nat.lt_or_ge n 439928057 with hs4 | hs4
          · -- n < 439928057
            rcases Nat.lt_or_ge n 439748201 with hs5 | hs5
            · -- n < 439748201
              exact Brocard.berndt_galway_chunk_2445 n m (by omega) (by omega) h
            · -- n >= 439748201
              exact Brocard.berndt_galway_chunk_2446 n m (by omega) (by omega) h
          · -- n >= 439928057
            exact Brocard.berndt_galway_chunk_2447 n m (by omega) (by omega) h
    · -- n >= 440107913
      rcases Nat.lt_or_ge n 441187050 with hs2 | hs2
      · -- n < 441187050
        rcases Nat.lt_or_ge n 440647482 with hs3 | hs3
        · -- n < 440647482
          rcases Nat.lt_or_ge n 440467625 with hs4 | hs4
          · -- n < 440467625
            rcases Nat.lt_or_ge n 440287769 with hs5 | hs5
            · -- n < 440287769
              exact Brocard.berndt_galway_chunk_2448 n m (by omega) (by omega) h
            · -- n >= 440287769
              exact Brocard.berndt_galway_chunk_2449 n m (by omega) (by omega) h
          · -- n >= 440467625
            exact Brocard.berndt_galway_chunk_2450 n m (by omega) (by omega) h
        · -- n >= 440647482
          rcases Nat.lt_or_ge n 441007194 with hs4 | hs4
          · -- n < 441007194
            rcases Nat.lt_or_ge n 440827338 with hs5 | hs5
            · -- n < 440827338
              exact Brocard.berndt_galway_chunk_2451 n m (by omega) (by omega) h
            · -- n >= 440827338
              exact Brocard.berndt_galway_chunk_2452 n m (by omega) (by omega) h
          · -- n >= 441007194
            exact Brocard.berndt_galway_chunk_2453 n m (by omega) (by omega) h
      · -- n >= 441187050
        rcases Nat.lt_or_ge n 441726618 with hs3 | hs3
        · -- n < 441726618
          rcases Nat.lt_or_ge n 441546762 with hs4 | hs4
          · -- n < 441546762
            rcases Nat.lt_or_ge n 441366906 with hs5 | hs5
            · -- n < 441366906
              exact Brocard.berndt_galway_chunk_2454 n m (by omega) (by omega) h
            · -- n >= 441366906
              exact Brocard.berndt_galway_chunk_2455 n m (by omega) (by omega) h
          · -- n >= 441546762
            exact Brocard.berndt_galway_chunk_2456 n m (by omega) (by omega) h
        · -- n >= 441726618
          rcases Nat.lt_or_ge n 441906474 with hs4 | hs4
          · -- n < 441906474
            exact Brocard.berndt_galway_chunk_2457 n m (by omega) (by omega) h
          · -- n >= 441906474
            exact Brocard.berndt_galway_chunk_2458 n m (by omega) (by omega) h
