-- Prove2me | solution 1 for Brocard.berndt_galway_group_060
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:52:03.497824+00:00
-- url     : https://prove2.me/submissions/122c38e7-971d-4265-b08d-6f98208283d1

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_2735
import Theorems.Thm_Brocard_berndt_galway_chunk_2736
import Theorems.Thm_Brocard_berndt_galway_chunk_2737
import Theorems.Thm_Brocard_berndt_galway_chunk_2738
import Theorems.Thm_Brocard_berndt_galway_chunk_2739
import Theorems.Thm_Brocard_berndt_galway_chunk_2740
import Theorems.Thm_Brocard_berndt_galway_chunk_2741
import Theorems.Thm_Brocard_berndt_galway_chunk_2742
import Theorems.Thm_Brocard_berndt_galway_chunk_2743
import Theorems.Thm_Brocard_berndt_galway_chunk_2744
import Theorems.Thm_Brocard_berndt_galway_chunk_2745
import Theorems.Thm_Brocard_berndt_galway_chunk_2746
import Theorems.Thm_Brocard_berndt_galway_chunk_2747
import Theorems.Thm_Brocard_berndt_galway_chunk_2748
import Theorems.Thm_Brocard_berndt_galway_chunk_2749
import Theorems.Thm_Brocard_berndt_galway_chunk_2750
import Theorems.Thm_Brocard_berndt_galway_chunk_2751
import Theorems.Thm_Brocard_berndt_galway_chunk_2752
import Theorems.Thm_Brocard_berndt_galway_chunk_2753
import Theorems.Thm_Brocard_berndt_galway_chunk_2754
import Theorems.Thm_Brocard_berndt_galway_chunk_2755
import Theorems.Thm_Brocard_berndt_galway_chunk_2756
import Theorems.Thm_Brocard_berndt_galway_chunk_2757
import Theorems.Thm_Brocard_berndt_galway_chunk_2758
import Theorems.Thm_Brocard_berndt_galway_chunk_2759
import Theorems.Thm_Brocard_berndt_galway_chunk_2760
import Theorems.Thm_Brocard_berndt_galway_chunk_2761
import Theorems.Thm_Brocard_berndt_galway_chunk_2762
import Theorems.Thm_Brocard_berndt_galway_chunk_2763
import Theorems.Thm_Brocard_berndt_galway_chunk_2764
import Theorems.Thm_Brocard_berndt_galway_chunk_2765
import Theorems.Thm_Brocard_berndt_galway_chunk_2766
import Theorems.Thm_Brocard_berndt_galway_chunk_2767
import Theorems.Thm_Brocard_berndt_galway_chunk_2768
import Theorems.Thm_Brocard_berndt_galway_chunk_2769
import Theorems.Thm_Brocard_berndt_galway_chunk_2770
import Theorems.Thm_Brocard_berndt_galway_chunk_2771
import Theorems.Thm_Brocard_berndt_galway_chunk_2772
import Theorems.Thm_Brocard_berndt_galway_chunk_2773
import Theorems.Thm_Brocard_berndt_galway_chunk_2774
import Theorems.Thm_Brocard_berndt_galway_chunk_2775
import Theorems.Thm_Brocard_berndt_galway_chunk_2776
import Theorems.Thm_Brocard_berndt_galway_chunk_2777
import Theorems.Thm_Brocard_berndt_galway_chunk_2778
import Theorems.Thm_Brocard_berndt_galway_chunk_2779
import Theorems.Thm_Brocard_berndt_galway_chunk_2780

theorem solution (n m : ℕ) (h1 : 491726618 ≤ n) (h2 : n < 500000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 495863309 with hs0 | hs0
  · -- n < 495863309
    rcases Nat.lt_or_ge n 493884892 with hs1 | hs1
    · -- n < 493884892
      rcases Nat.lt_or_ge n 492805755 with hs2 | hs2
      · -- n < 492805755
        rcases Nat.lt_or_ge n 492266187 with hs3 | hs3
        · -- n < 492266187
          rcases Nat.lt_or_ge n 492086330 with hs4 | hs4
          · -- n < 492086330
            rcases Nat.lt_or_ge n 491906474 with hs5 | hs5
            · -- n < 491906474
              exact Brocard.berndt_galway_chunk_2735 n m (by omega) (by omega) h
            · -- n >= 491906474
              exact Brocard.berndt_galway_chunk_2736 n m (by omega) (by omega) h
          · -- n >= 492086330
            exact Brocard.berndt_galway_chunk_2737 n m (by omega) (by omega) h
        · -- n >= 492266187
          rcases Nat.lt_or_ge n 492625899 with hs4 | hs4
          · -- n < 492625899
            rcases Nat.lt_or_ge n 492446043 with hs5 | hs5
            · -- n < 492446043
              exact Brocard.berndt_galway_chunk_2738 n m (by omega) (by omega) h
            · -- n >= 492446043
              exact Brocard.berndt_galway_chunk_2739 n m (by omega) (by omega) h
          · -- n >= 492625899
            exact Brocard.berndt_galway_chunk_2740 n m (by omega) (by omega) h
      · -- n >= 492805755
        rcases Nat.lt_or_ge n 493345323 with hs3 | hs3
        · -- n < 493345323
          rcases Nat.lt_or_ge n 493165467 with hs4 | hs4
          · -- n < 493165467
            rcases Nat.lt_or_ge n 492985611 with hs5 | hs5
            · -- n < 492985611
              exact Brocard.berndt_galway_chunk_2741 n m (by omega) (by omega) h
            · -- n >= 492985611
              exact Brocard.berndt_galway_chunk_2742 n m (by omega) (by omega) h
          · -- n >= 493165467
            exact Brocard.berndt_galway_chunk_2743 n m (by omega) (by omega) h
        · -- n >= 493345323
          rcases Nat.lt_or_ge n 493705035 with hs4 | hs4
          · -- n < 493705035
            rcases Nat.lt_or_ge n 493525179 with hs5 | hs5
            · -- n < 493525179
              exact Brocard.berndt_galway_chunk_2744 n m (by omega) (by omega) h
            · -- n >= 493525179
              exact Brocard.berndt_galway_chunk_2745 n m (by omega) (by omega) h
          · -- n >= 493705035
            exact Brocard.berndt_galway_chunk_2746 n m (by omega) (by omega) h
    · -- n >= 493884892
      rcases Nat.lt_or_ge n 494964028 with hs2 | hs2
      · -- n < 494964028
        rcases Nat.lt_or_ge n 494424460 with hs3 | hs3
        · -- n < 494424460
          rcases Nat.lt_or_ge n 494244604 with hs4 | hs4
          · -- n < 494244604
            rcases Nat.lt_or_ge n 494064748 with hs5 | hs5
            · -- n < 494064748
              exact Brocard.berndt_galway_chunk_2747 n m (by omega) (by omega) h
            · -- n >= 494064748
              exact Brocard.berndt_galway_chunk_2748 n m (by omega) (by omega) h
          · -- n >= 494244604
            exact Brocard.berndt_galway_chunk_2749 n m (by omega) (by omega) h
        · -- n >= 494424460
          rcases Nat.lt_or_ge n 494784172 with hs4 | hs4
          · -- n < 494784172
            rcases Nat.lt_or_ge n 494604316 with hs5 | hs5
            · -- n < 494604316
              exact Brocard.berndt_galway_chunk_2750 n m (by omega) (by omega) h
            · -- n >= 494604316
              exact Brocard.berndt_galway_chunk_2751 n m (by omega) (by omega) h
          · -- n >= 494784172
            exact Brocard.berndt_galway_chunk_2752 n m (by omega) (by omega) h
      · -- n >= 494964028
        rcases Nat.lt_or_ge n 495503597 with hs3 | hs3
        · -- n < 495503597
          rcases Nat.lt_or_ge n 495323741 with hs4 | hs4
          · -- n < 495323741
            rcases Nat.lt_or_ge n 495143884 with hs5 | hs5
            · -- n < 495143884
              exact Brocard.berndt_galway_chunk_2753 n m (by omega) (by omega) h
            · -- n >= 495143884
              exact Brocard.berndt_galway_chunk_2754 n m (by omega) (by omega) h
          · -- n >= 495323741
            exact Brocard.berndt_galway_chunk_2755 n m (by omega) (by omega) h
        · -- n >= 495503597
          rcases Nat.lt_or_ge n 495683453 with hs4 | hs4
          · -- n < 495683453
            exact Brocard.berndt_galway_chunk_2756 n m (by omega) (by omega) h
          · -- n >= 495683453
            exact Brocard.berndt_galway_chunk_2757 n m (by omega) (by omega) h
  · -- n >= 495863309
    rcases Nat.lt_or_ge n 498021582 with hs1 | hs1
    · -- n < 498021582
      rcases Nat.lt_or_ge n 496942446 with hs2 | hs2
      · -- n < 496942446
        rcases Nat.lt_or_ge n 496402877 with hs3 | hs3
        · -- n < 496402877
          rcases Nat.lt_or_ge n 496223021 with hs4 | hs4
          · -- n < 496223021
            rcases Nat.lt_or_ge n 496043165 with hs5 | hs5
            · -- n < 496043165
              exact Brocard.berndt_galway_chunk_2758 n m (by omega) (by omega) h
            · -- n >= 496043165
              exact Brocard.berndt_galway_chunk_2759 n m (by omega) (by omega) h
          · -- n >= 496223021
            exact Brocard.berndt_galway_chunk_2760 n m (by omega) (by omega) h
        · -- n >= 496402877
          rcases Nat.lt_or_ge n 496762589 with hs4 | hs4
          · -- n < 496762589
            rcases Nat.lt_or_ge n 496582733 with hs5 | hs5
            · -- n < 496582733
              exact Brocard.berndt_galway_chunk_2761 n m (by omega) (by omega) h
            · -- n >= 496582733
              exact Brocard.berndt_galway_chunk_2762 n m (by omega) (by omega) h
          · -- n >= 496762589
            exact Brocard.berndt_galway_chunk_2763 n m (by omega) (by omega) h
      · -- n >= 496942446
        rcases Nat.lt_or_ge n 497482014 with hs3 | hs3
        · -- n < 497482014
          rcases Nat.lt_or_ge n 497302158 with hs4 | hs4
          · -- n < 497302158
            rcases Nat.lt_or_ge n 497122302 with hs5 | hs5
            · -- n < 497122302
              exact Brocard.berndt_galway_chunk_2764 n m (by omega) (by omega) h
            · -- n >= 497122302
              exact Brocard.berndt_galway_chunk_2765 n m (by omega) (by omega) h
          · -- n >= 497302158
            exact Brocard.berndt_galway_chunk_2766 n m (by omega) (by omega) h
        · -- n >= 497482014
          rcases Nat.lt_or_ge n 497841726 with hs4 | hs4
          · -- n < 497841726
            rcases Nat.lt_or_ge n 497661870 with hs5 | hs5
            · -- n < 497661870
              exact Brocard.berndt_galway_chunk_2767 n m (by omega) (by omega) h
            · -- n >= 497661870
              exact Brocard.berndt_galway_chunk_2768 n m (by omega) (by omega) h
          · -- n >= 497841726
            exact Brocard.berndt_galway_chunk_2769 n m (by omega) (by omega) h
    · -- n >= 498021582
      rcases Nat.lt_or_ge n 499100719 with hs2 | hs2
      · -- n < 499100719
        rcases Nat.lt_or_ge n 498561151 with hs3 | hs3
        · -- n < 498561151
          rcases Nat.lt_or_ge n 498381294 with hs4 | hs4
          · -- n < 498381294
            rcases Nat.lt_or_ge n 498201438 with hs5 | hs5
            · -- n < 498201438
              exact Brocard.berndt_galway_chunk_2770 n m (by omega) (by omega) h
            · -- n >= 498201438
              exact Brocard.berndt_galway_chunk_2771 n m (by omega) (by omega) h
          · -- n >= 498381294
            exact Brocard.berndt_galway_chunk_2772 n m (by omega) (by omega) h
        · -- n >= 498561151
          rcases Nat.lt_or_ge n 498920863 with hs4 | hs4
          · -- n < 498920863
            rcases Nat.lt_or_ge n 498741007 with hs5 | hs5
            · -- n < 498741007
              exact Brocard.berndt_galway_chunk_2773 n m (by omega) (by omega) h
            · -- n >= 498741007
              exact Brocard.berndt_galway_chunk_2774 n m (by omega) (by omega) h
          · -- n >= 498920863
            exact Brocard.berndt_galway_chunk_2775 n m (by omega) (by omega) h
      · -- n >= 499100719
        rcases Nat.lt_or_ge n 499640287 with hs3 | hs3
        · -- n < 499640287
          rcases Nat.lt_or_ge n 499460431 with hs4 | hs4
          · -- n < 499460431
            rcases Nat.lt_or_ge n 499280575 with hs5 | hs5
            · -- n < 499280575
              exact Brocard.berndt_galway_chunk_2776 n m (by omega) (by omega) h
            · -- n >= 499280575
              exact Brocard.berndt_galway_chunk_2777 n m (by omega) (by omega) h
          · -- n >= 499460431
            exact Brocard.berndt_galway_chunk_2778 n m (by omega) (by omega) h
        · -- n >= 499640287
          rcases Nat.lt_or_ge n 499820143 with hs4 | hs4
          · -- n < 499820143
            exact Brocard.berndt_galway_chunk_2779 n m (by omega) (by omega) h
          · -- n >= 499820143
            exact Brocard.berndt_galway_chunk_2780 n m (by omega) (by omega) h
