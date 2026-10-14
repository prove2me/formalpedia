-- Prove2me | solution 1 for Brocard.berndt_galway_group_056
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:20:30.787067+00:00
-- url     : https://prove2.me/submissions/849c3d96-b2ce-446a-97ae-325d3017803b

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_2551
import Theorems.Thm_Brocard_berndt_galway_chunk_2552
import Theorems.Thm_Brocard_berndt_galway_chunk_2553
import Theorems.Thm_Brocard_berndt_galway_chunk_2554
import Theorems.Thm_Brocard_berndt_galway_chunk_2555
import Theorems.Thm_Brocard_berndt_galway_chunk_2556
import Theorems.Thm_Brocard_berndt_galway_chunk_2557
import Theorems.Thm_Brocard_berndt_galway_chunk_2558
import Theorems.Thm_Brocard_berndt_galway_chunk_2559
import Theorems.Thm_Brocard_berndt_galway_chunk_2560
import Theorems.Thm_Brocard_berndt_galway_chunk_2561
import Theorems.Thm_Brocard_berndt_galway_chunk_2562
import Theorems.Thm_Brocard_berndt_galway_chunk_2563
import Theorems.Thm_Brocard_berndt_galway_chunk_2564
import Theorems.Thm_Brocard_berndt_galway_chunk_2565
import Theorems.Thm_Brocard_berndt_galway_chunk_2566
import Theorems.Thm_Brocard_berndt_galway_chunk_2567
import Theorems.Thm_Brocard_berndt_galway_chunk_2568
import Theorems.Thm_Brocard_berndt_galway_chunk_2569
import Theorems.Thm_Brocard_berndt_galway_chunk_2570
import Theorems.Thm_Brocard_berndt_galway_chunk_2571
import Theorems.Thm_Brocard_berndt_galway_chunk_2572
import Theorems.Thm_Brocard_berndt_galway_chunk_2573
import Theorems.Thm_Brocard_berndt_galway_chunk_2574
import Theorems.Thm_Brocard_berndt_galway_chunk_2575
import Theorems.Thm_Brocard_berndt_galway_chunk_2576
import Theorems.Thm_Brocard_berndt_galway_chunk_2577
import Theorems.Thm_Brocard_berndt_galway_chunk_2578
import Theorems.Thm_Brocard_berndt_galway_chunk_2579
import Theorems.Thm_Brocard_berndt_galway_chunk_2580
import Theorems.Thm_Brocard_berndt_galway_chunk_2581
import Theorems.Thm_Brocard_berndt_galway_chunk_2582
import Theorems.Thm_Brocard_berndt_galway_chunk_2583
import Theorems.Thm_Brocard_berndt_galway_chunk_2584
import Theorems.Thm_Brocard_berndt_galway_chunk_2585
import Theorems.Thm_Brocard_berndt_galway_chunk_2586
import Theorems.Thm_Brocard_berndt_galway_chunk_2587
import Theorems.Thm_Brocard_berndt_galway_chunk_2588
import Theorems.Thm_Brocard_berndt_galway_chunk_2589
import Theorems.Thm_Brocard_berndt_galway_chunk_2590
import Theorems.Thm_Brocard_berndt_galway_chunk_2591
import Theorems.Thm_Brocard_berndt_galway_chunk_2592
import Theorems.Thm_Brocard_berndt_galway_chunk_2593
import Theorems.Thm_Brocard_berndt_galway_chunk_2594
import Theorems.Thm_Brocard_berndt_galway_chunk_2595
import Theorems.Thm_Brocard_berndt_galway_chunk_2596

theorem solution (n m : ℕ) (h1 : 458633093 ≤ n) (h2 : n < 466906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 462769784 with hs0 | hs0
  · -- n < 462769784
    rcases Nat.lt_or_ge n 460791366 with hs1 | hs1
    · -- n < 460791366
      rcases Nat.lt_or_ge n 459712230 with hs2 | hs2
      · -- n < 459712230
        rcases Nat.lt_or_ge n 459172661 with hs3 | hs3
        · -- n < 459172661
          rcases Nat.lt_or_ge n 458992805 with hs4 | hs4
          · -- n < 458992805
            rcases Nat.lt_or_ge n 458812949 with hs5 | hs5
            · -- n < 458812949
              exact Brocard.berndt_galway_chunk_2551 n m (by omega) (by omega) h
            · -- n >= 458812949
              exact Brocard.berndt_galway_chunk_2552 n m (by omega) (by omega) h
          · -- n >= 458992805
            exact Brocard.berndt_galway_chunk_2553 n m (by omega) (by omega) h
        · -- n >= 459172661
          rcases Nat.lt_or_ge n 459532374 with hs4 | hs4
          · -- n < 459532374
            rcases Nat.lt_or_ge n 459352517 with hs5 | hs5
            · -- n < 459352517
              exact Brocard.berndt_galway_chunk_2554 n m (by omega) (by omega) h
            · -- n >= 459352517
              exact Brocard.berndt_galway_chunk_2555 n m (by omega) (by omega) h
          · -- n >= 459532374
            exact Brocard.berndt_galway_chunk_2556 n m (by omega) (by omega) h
      · -- n >= 459712230
        rcases Nat.lt_or_ge n 460251798 with hs3 | hs3
        · -- n < 460251798
          rcases Nat.lt_or_ge n 460071942 with hs4 | hs4
          · -- n < 460071942
            rcases Nat.lt_or_ge n 459892086 with hs5 | hs5
            · -- n < 459892086
              exact Brocard.berndt_galway_chunk_2557 n m (by omega) (by omega) h
            · -- n >= 459892086
              exact Brocard.berndt_galway_chunk_2558 n m (by omega) (by omega) h
          · -- n >= 460071942
            exact Brocard.berndt_galway_chunk_2559 n m (by omega) (by omega) h
        · -- n >= 460251798
          rcases Nat.lt_or_ge n 460611510 with hs4 | hs4
          · -- n < 460611510
            rcases Nat.lt_or_ge n 460431654 with hs5 | hs5
            · -- n < 460431654
              exact Brocard.berndt_galway_chunk_2560 n m (by omega) (by omega) h
            · -- n >= 460431654
              exact Brocard.berndt_galway_chunk_2561 n m (by omega) (by omega) h
          · -- n >= 460611510
            exact Brocard.berndt_galway_chunk_2562 n m (by omega) (by omega) h
    · -- n >= 460791366
      rcases Nat.lt_or_ge n 461870503 with hs2 | hs2
      · -- n < 461870503
        rcases Nat.lt_or_ge n 461330935 with hs3 | hs3
        · -- n < 461330935
          rcases Nat.lt_or_ge n 461151079 with hs4 | hs4
          · -- n < 461151079
            rcases Nat.lt_or_ge n 460971223 with hs5 | hs5
            · -- n < 460971223
              exact Brocard.berndt_galway_chunk_2563 n m (by omega) (by omega) h
            · -- n >= 460971223
              exact Brocard.berndt_galway_chunk_2564 n m (by omega) (by omega) h
          · -- n >= 461151079
            exact Brocard.berndt_galway_chunk_2565 n m (by omega) (by omega) h
        · -- n >= 461330935
          rcases Nat.lt_or_ge n 461690647 with hs4 | hs4
          · -- n < 461690647
            rcases Nat.lt_or_ge n 461510791 with hs5 | hs5
            · -- n < 461510791
              exact Brocard.berndt_galway_chunk_2566 n m (by omega) (by omega) h
            · -- n >= 461510791
              exact Brocard.berndt_galway_chunk_2567 n m (by omega) (by omega) h
          · -- n >= 461690647
            exact Brocard.berndt_galway_chunk_2568 n m (by omega) (by omega) h
      · -- n >= 461870503
        rcases Nat.lt_or_ge n 462410071 with hs3 | hs3
        · -- n < 462410071
          rcases Nat.lt_or_ge n 462230215 with hs4 | hs4
          · -- n < 462230215
            rcases Nat.lt_or_ge n 462050359 with hs5 | hs5
            · -- n < 462050359
              exact Brocard.berndt_galway_chunk_2569 n m (by omega) (by omega) h
            · -- n >= 462050359
              exact Brocard.berndt_galway_chunk_2570 n m (by omega) (by omega) h
          · -- n >= 462230215
            exact Brocard.berndt_galway_chunk_2571 n m (by omega) (by omega) h
        · -- n >= 462410071
          rcases Nat.lt_or_ge n 462589928 with hs4 | hs4
          · -- n < 462589928
            exact Brocard.berndt_galway_chunk_2572 n m (by omega) (by omega) h
          · -- n >= 462589928
            exact Brocard.berndt_galway_chunk_2573 n m (by omega) (by omega) h
  · -- n >= 462769784
    rcases Nat.lt_or_ge n 464928057 with hs1 | hs1
    · -- n < 464928057
      rcases Nat.lt_or_ge n 463848920 with hs2 | hs2
      · -- n < 463848920
        rcases Nat.lt_or_ge n 463309352 with hs3 | hs3
        · -- n < 463309352
          rcases Nat.lt_or_ge n 463129496 with hs4 | hs4
          · -- n < 463129496
            rcases Nat.lt_or_ge n 462949640 with hs5 | hs5
            · -- n < 462949640
              exact Brocard.berndt_galway_chunk_2574 n m (by omega) (by omega) h
            · -- n >= 462949640
              exact Brocard.berndt_galway_chunk_2575 n m (by omega) (by omega) h
          · -- n >= 463129496
            exact Brocard.berndt_galway_chunk_2576 n m (by omega) (by omega) h
        · -- n >= 463309352
          rcases Nat.lt_or_ge n 463669064 with hs4 | hs4
          · -- n < 463669064
            rcases Nat.lt_or_ge n 463489208 with hs5 | hs5
            · -- n < 463489208
              exact Brocard.berndt_galway_chunk_2577 n m (by omega) (by omega) h
            · -- n >= 463489208
              exact Brocard.berndt_galway_chunk_2578 n m (by omega) (by omega) h
          · -- n >= 463669064
            exact Brocard.berndt_galway_chunk_2579 n m (by omega) (by omega) h
      · -- n >= 463848920
        rcases Nat.lt_or_ge n 464388489 with hs3 | hs3
        · -- n < 464388489
          rcases Nat.lt_or_ge n 464208633 with hs4 | hs4
          · -- n < 464208633
            rcases Nat.lt_or_ge n 464028776 with hs5 | hs5
            · -- n < 464028776
              exact Brocard.berndt_galway_chunk_2580 n m (by omega) (by omega) h
            · -- n >= 464028776
              exact Brocard.berndt_galway_chunk_2581 n m (by omega) (by omega) h
          · -- n >= 464208633
            exact Brocard.berndt_galway_chunk_2582 n m (by omega) (by omega) h
        · -- n >= 464388489
          rcases Nat.lt_or_ge n 464748201 with hs4 | hs4
          · -- n < 464748201
            rcases Nat.lt_or_ge n 464568345 with hs5 | hs5
            · -- n < 464568345
              exact Brocard.berndt_galway_chunk_2583 n m (by omega) (by omega) h
            · -- n >= 464568345
              exact Brocard.berndt_galway_chunk_2584 n m (by omega) (by omega) h
          · -- n >= 464748201
            exact Brocard.berndt_galway_chunk_2585 n m (by omega) (by omega) h
    · -- n >= 464928057
      rcases Nat.lt_or_ge n 466007194 with hs2 | hs2
      · -- n < 466007194
        rcases Nat.lt_or_ge n 465467625 with hs3 | hs3
        · -- n < 465467625
          rcases Nat.lt_or_ge n 465287769 with hs4 | hs4
          · -- n < 465287769
            rcases Nat.lt_or_ge n 465107913 with hs5 | hs5
            · -- n < 465107913
              exact Brocard.berndt_galway_chunk_2586 n m (by omega) (by omega) h
            · -- n >= 465107913
              exact Brocard.berndt_galway_chunk_2587 n m (by omega) (by omega) h
          · -- n >= 465287769
            exact Brocard.berndt_galway_chunk_2588 n m (by omega) (by omega) h
        · -- n >= 465467625
          rcases Nat.lt_or_ge n 465827338 with hs4 | hs4
          · -- n < 465827338
            rcases Nat.lt_or_ge n 465647482 with hs5 | hs5
            · -- n < 465647482
              exact Brocard.berndt_galway_chunk_2589 n m (by omega) (by omega) h
            · -- n >= 465647482
              exact Brocard.berndt_galway_chunk_2590 n m (by omega) (by omega) h
          · -- n >= 465827338
            exact Brocard.berndt_galway_chunk_2591 n m (by omega) (by omega) h
      · -- n >= 466007194
        rcases Nat.lt_or_ge n 466546762 with hs3 | hs3
        · -- n < 466546762
          rcases Nat.lt_or_ge n 466366906 with hs4 | hs4
          · -- n < 466366906
            rcases Nat.lt_or_ge n 466187050 with hs5 | hs5
            · -- n < 466187050
              exact Brocard.berndt_galway_chunk_2592 n m (by omega) (by omega) h
            · -- n >= 466187050
              exact Brocard.berndt_galway_chunk_2593 n m (by omega) (by omega) h
          · -- n >= 466366906
            exact Brocard.berndt_galway_chunk_2594 n m (by omega) (by omega) h
        · -- n >= 466546762
          rcases Nat.lt_or_ge n 466726618 with hs4 | hs4
          · -- n < 466726618
            exact Brocard.berndt_galway_chunk_2595 n m (by omega) (by omega) h
          · -- n >= 466726618
            exact Brocard.berndt_galway_chunk_2596 n m (by omega) (by omega) h
