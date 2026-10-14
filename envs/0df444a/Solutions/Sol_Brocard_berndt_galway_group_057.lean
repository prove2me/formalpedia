-- Prove2me | solution 1 for Brocard.berndt_galway_group_057
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:29:49.307301+00:00
-- url     : https://prove2.me/submissions/c304e2f9-8fa7-432b-8c3c-627dab41ab15

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_2597
import Theorems.Thm_Brocard_berndt_galway_chunk_2598
import Theorems.Thm_Brocard_berndt_galway_chunk_2599
import Theorems.Thm_Brocard_berndt_galway_chunk_2600
import Theorems.Thm_Brocard_berndt_galway_chunk_2601
import Theorems.Thm_Brocard_berndt_galway_chunk_2602
import Theorems.Thm_Brocard_berndt_galway_chunk_2603
import Theorems.Thm_Brocard_berndt_galway_chunk_2604
import Theorems.Thm_Brocard_berndt_galway_chunk_2605
import Theorems.Thm_Brocard_berndt_galway_chunk_2606
import Theorems.Thm_Brocard_berndt_galway_chunk_2607
import Theorems.Thm_Brocard_berndt_galway_chunk_2608
import Theorems.Thm_Brocard_berndt_galway_chunk_2609
import Theorems.Thm_Brocard_berndt_galway_chunk_2610
import Theorems.Thm_Brocard_berndt_galway_chunk_2611
import Theorems.Thm_Brocard_berndt_galway_chunk_2612
import Theorems.Thm_Brocard_berndt_galway_chunk_2613
import Theorems.Thm_Brocard_berndt_galway_chunk_2614
import Theorems.Thm_Brocard_berndt_galway_chunk_2615
import Theorems.Thm_Brocard_berndt_galway_chunk_2616
import Theorems.Thm_Brocard_berndt_galway_chunk_2617
import Theorems.Thm_Brocard_berndt_galway_chunk_2618
import Theorems.Thm_Brocard_berndt_galway_chunk_2619
import Theorems.Thm_Brocard_berndt_galway_chunk_2620
import Theorems.Thm_Brocard_berndt_galway_chunk_2621
import Theorems.Thm_Brocard_berndt_galway_chunk_2622
import Theorems.Thm_Brocard_berndt_galway_chunk_2623
import Theorems.Thm_Brocard_berndt_galway_chunk_2624
import Theorems.Thm_Brocard_berndt_galway_chunk_2625
import Theorems.Thm_Brocard_berndt_galway_chunk_2626
import Theorems.Thm_Brocard_berndt_galway_chunk_2627
import Theorems.Thm_Brocard_berndt_galway_chunk_2628
import Theorems.Thm_Brocard_berndt_galway_chunk_2629
import Theorems.Thm_Brocard_berndt_galway_chunk_2630
import Theorems.Thm_Brocard_berndt_galway_chunk_2631
import Theorems.Thm_Brocard_berndt_galway_chunk_2632
import Theorems.Thm_Brocard_berndt_galway_chunk_2633
import Theorems.Thm_Brocard_berndt_galway_chunk_2634
import Theorems.Thm_Brocard_berndt_galway_chunk_2635
import Theorems.Thm_Brocard_berndt_galway_chunk_2636
import Theorems.Thm_Brocard_berndt_galway_chunk_2637
import Theorems.Thm_Brocard_berndt_galway_chunk_2638
import Theorems.Thm_Brocard_berndt_galway_chunk_2639
import Theorems.Thm_Brocard_berndt_galway_chunk_2640
import Theorems.Thm_Brocard_berndt_galway_chunk_2641
import Theorems.Thm_Brocard_berndt_galway_chunk_2642

theorem solution (n m : ℕ) (h1 : 466906474 ≤ n) (h2 : n < 475179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 471043165 with hs0 | hs0
  · -- n < 471043165
    rcases Nat.lt_or_ge n 469064748 with hs1 | hs1
    · -- n < 469064748
      rcases Nat.lt_or_ge n 467985611 with hs2 | hs2
      · -- n < 467985611
        rcases Nat.lt_or_ge n 467446043 with hs3 | hs3
        · -- n < 467446043
          rcases Nat.lt_or_ge n 467266187 with hs4 | hs4
          · -- n < 467266187
            rcases Nat.lt_or_ge n 467086330 with hs5 | hs5
            · -- n < 467086330
              exact Brocard.berndt_galway_chunk_2597 n m (by omega) (by omega) h
            · -- n >= 467086330
              exact Brocard.berndt_galway_chunk_2598 n m (by omega) (by omega) h
          · -- n >= 467266187
            exact Brocard.berndt_galway_chunk_2599 n m (by omega) (by omega) h
        · -- n >= 467446043
          rcases Nat.lt_or_ge n 467805755 with hs4 | hs4
          · -- n < 467805755
            rcases Nat.lt_or_ge n 467625899 with hs5 | hs5
            · -- n < 467625899
              exact Brocard.berndt_galway_chunk_2600 n m (by omega) (by omega) h
            · -- n >= 467625899
              exact Brocard.berndt_galway_chunk_2601 n m (by omega) (by omega) h
          · -- n >= 467805755
            exact Brocard.berndt_galway_chunk_2602 n m (by omega) (by omega) h
      · -- n >= 467985611
        rcases Nat.lt_or_ge n 468525179 with hs3 | hs3
        · -- n < 468525179
          rcases Nat.lt_or_ge n 468345323 with hs4 | hs4
          · -- n < 468345323
            rcases Nat.lt_or_ge n 468165467 with hs5 | hs5
            · -- n < 468165467
              exact Brocard.berndt_galway_chunk_2603 n m (by omega) (by omega) h
            · -- n >= 468165467
              exact Brocard.berndt_galway_chunk_2604 n m (by omega) (by omega) h
          · -- n >= 468345323
            exact Brocard.berndt_galway_chunk_2605 n m (by omega) (by omega) h
        · -- n >= 468525179
          rcases Nat.lt_or_ge n 468884892 with hs4 | hs4
          · -- n < 468884892
            rcases Nat.lt_or_ge n 468705035 with hs5 | hs5
            · -- n < 468705035
              exact Brocard.berndt_galway_chunk_2606 n m (by omega) (by omega) h
            · -- n >= 468705035
              exact Brocard.berndt_galway_chunk_2607 n m (by omega) (by omega) h
          · -- n >= 468884892
            exact Brocard.berndt_galway_chunk_2608 n m (by omega) (by omega) h
    · -- n >= 469064748
      rcases Nat.lt_or_ge n 470143884 with hs2 | hs2
      · -- n < 470143884
        rcases Nat.lt_or_ge n 469604316 with hs3 | hs3
        · -- n < 469604316
          rcases Nat.lt_or_ge n 469424460 with hs4 | hs4
          · -- n < 469424460
            rcases Nat.lt_or_ge n 469244604 with hs5 | hs5
            · -- n < 469244604
              exact Brocard.berndt_galway_chunk_2609 n m (by omega) (by omega) h
            · -- n >= 469244604
              exact Brocard.berndt_galway_chunk_2610 n m (by omega) (by omega) h
          · -- n >= 469424460
            exact Brocard.berndt_galway_chunk_2611 n m (by omega) (by omega) h
        · -- n >= 469604316
          rcases Nat.lt_or_ge n 469964028 with hs4 | hs4
          · -- n < 469964028
            rcases Nat.lt_or_ge n 469784172 with hs5 | hs5
            · -- n < 469784172
              exact Brocard.berndt_galway_chunk_2612 n m (by omega) (by omega) h
            · -- n >= 469784172
              exact Brocard.berndt_galway_chunk_2613 n m (by omega) (by omega) h
          · -- n >= 469964028
            exact Brocard.berndt_galway_chunk_2614 n m (by omega) (by omega) h
      · -- n >= 470143884
        rcases Nat.lt_or_ge n 470683453 with hs3 | hs3
        · -- n < 470683453
          rcases Nat.lt_or_ge n 470503597 with hs4 | hs4
          · -- n < 470503597
            rcases Nat.lt_or_ge n 470323741 with hs5 | hs5
            · -- n < 470323741
              exact Brocard.berndt_galway_chunk_2615 n m (by omega) (by omega) h
            · -- n >= 470323741
              exact Brocard.berndt_galway_chunk_2616 n m (by omega) (by omega) h
          · -- n >= 470503597
            exact Brocard.berndt_galway_chunk_2617 n m (by omega) (by omega) h
        · -- n >= 470683453
          rcases Nat.lt_or_ge n 470863309 with hs4 | hs4
          · -- n < 470863309
            exact Brocard.berndt_galway_chunk_2618 n m (by omega) (by omega) h
          · -- n >= 470863309
            exact Brocard.berndt_galway_chunk_2619 n m (by omega) (by omega) h
  · -- n >= 471043165
    rcases Nat.lt_or_ge n 473201438 with hs1 | hs1
    · -- n < 473201438
      rcases Nat.lt_or_ge n 472122302 with hs2 | hs2
      · -- n < 472122302
        rcases Nat.lt_or_ge n 471582733 with hs3 | hs3
        · -- n < 471582733
          rcases Nat.lt_or_ge n 471402877 with hs4 | hs4
          · -- n < 471402877
            rcases Nat.lt_or_ge n 471223021 with hs5 | hs5
            · -- n < 471223021
              exact Brocard.berndt_galway_chunk_2620 n m (by omega) (by omega) h
            · -- n >= 471223021
              exact Brocard.berndt_galway_chunk_2621 n m (by omega) (by omega) h
          · -- n >= 471402877
            exact Brocard.berndt_galway_chunk_2622 n m (by omega) (by omega) h
        · -- n >= 471582733
          rcases Nat.lt_or_ge n 471942446 with hs4 | hs4
          · -- n < 471942446
            rcases Nat.lt_or_ge n 471762589 with hs5 | hs5
            · -- n < 471762589
              exact Brocard.berndt_galway_chunk_2623 n m (by omega) (by omega) h
            · -- n >= 471762589
              exact Brocard.berndt_galway_chunk_2624 n m (by omega) (by omega) h
          · -- n >= 471942446
            exact Brocard.berndt_galway_chunk_2625 n m (by omega) (by omega) h
      · -- n >= 472122302
        rcases Nat.lt_or_ge n 472661870 with hs3 | hs3
        · -- n < 472661870
          rcases Nat.lt_or_ge n 472482014 with hs4 | hs4
          · -- n < 472482014
            rcases Nat.lt_or_ge n 472302158 with hs5 | hs5
            · -- n < 472302158
              exact Brocard.berndt_galway_chunk_2626 n m (by omega) (by omega) h
            · -- n >= 472302158
              exact Brocard.berndt_galway_chunk_2627 n m (by omega) (by omega) h
          · -- n >= 472482014
            exact Brocard.berndt_galway_chunk_2628 n m (by omega) (by omega) h
        · -- n >= 472661870
          rcases Nat.lt_or_ge n 473021582 with hs4 | hs4
          · -- n < 473021582
            rcases Nat.lt_or_ge n 472841726 with hs5 | hs5
            · -- n < 472841726
              exact Brocard.berndt_galway_chunk_2629 n m (by omega) (by omega) h
            · -- n >= 472841726
              exact Brocard.berndt_galway_chunk_2630 n m (by omega) (by omega) h
          · -- n >= 473021582
            exact Brocard.berndt_galway_chunk_2631 n m (by omega) (by omega) h
    · -- n >= 473201438
      rcases Nat.lt_or_ge n 474280575 with hs2 | hs2
      · -- n < 474280575
        rcases Nat.lt_or_ge n 473741007 with hs3 | hs3
        · -- n < 473741007
          rcases Nat.lt_or_ge n 473561151 with hs4 | hs4
          · -- n < 473561151
            rcases Nat.lt_or_ge n 473381294 with hs5 | hs5
            · -- n < 473381294
              exact Brocard.berndt_galway_chunk_2632 n m (by omega) (by omega) h
            · -- n >= 473381294
              exact Brocard.berndt_galway_chunk_2633 n m (by omega) (by omega) h
          · -- n >= 473561151
            exact Brocard.berndt_galway_chunk_2634 n m (by omega) (by omega) h
        · -- n >= 473741007
          rcases Nat.lt_or_ge n 474100719 with hs4 | hs4
          · -- n < 474100719
            rcases Nat.lt_or_ge n 473920863 with hs5 | hs5
            · -- n < 473920863
              exact Brocard.berndt_galway_chunk_2635 n m (by omega) (by omega) h
            · -- n >= 473920863
              exact Brocard.berndt_galway_chunk_2636 n m (by omega) (by omega) h
          · -- n >= 474100719
            exact Brocard.berndt_galway_chunk_2637 n m (by omega) (by omega) h
      · -- n >= 474280575
        rcases Nat.lt_or_ge n 474820143 with hs3 | hs3
        · -- n < 474820143
          rcases Nat.lt_or_ge n 474640287 with hs4 | hs4
          · -- n < 474640287
            rcases Nat.lt_or_ge n 474460431 with hs5 | hs5
            · -- n < 474460431
              exact Brocard.berndt_galway_chunk_2638 n m (by omega) (by omega) h
            · -- n >= 474460431
              exact Brocard.berndt_galway_chunk_2639 n m (by omega) (by omega) h
          · -- n >= 474640287
            exact Brocard.berndt_galway_chunk_2640 n m (by omega) (by omega) h
        · -- n >= 474820143
          rcases Nat.lt_or_ge n 475000000 with hs4 | hs4
          · -- n < 475000000
            exact Brocard.berndt_galway_chunk_2641 n m (by omega) (by omega) h
          · -- n >= 475000000
            exact Brocard.berndt_galway_chunk_2642 n m (by omega) (by omega) h
