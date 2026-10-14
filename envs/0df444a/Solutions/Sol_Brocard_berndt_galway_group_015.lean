-- Prove2me | solution 1 for Brocard.berndt_galway_group_015
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:27:52.283999+00:00
-- url     : https://prove2.me/submissions/da558e6c-c27f-422e-b21f-469aad998b40

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_0651
import Theorems.Thm_Brocard_berndt_galway_chunk_0652
import Theorems.Thm_Brocard_berndt_galway_chunk_0653
import Theorems.Thm_Brocard_berndt_galway_chunk_0654
import Theorems.Thm_Brocard_berndt_galway_chunk_0655
import Theorems.Thm_Brocard_berndt_galway_chunk_0656
import Theorems.Thm_Brocard_berndt_galway_chunk_0657
import Theorems.Thm_Brocard_berndt_galway_chunk_0658
import Theorems.Thm_Brocard_berndt_galway_chunk_0659
import Theorems.Thm_Brocard_berndt_galway_chunk_0660
import Theorems.Thm_Brocard_berndt_galway_chunk_0661
import Theorems.Thm_Brocard_berndt_galway_chunk_0662
import Theorems.Thm_Brocard_berndt_galway_chunk_0663
import Theorems.Thm_Brocard_berndt_galway_chunk_0664
import Theorems.Thm_Brocard_berndt_galway_chunk_0665
import Theorems.Thm_Brocard_berndt_galway_chunk_0666
import Theorems.Thm_Brocard_berndt_galway_chunk_0667
import Theorems.Thm_Brocard_berndt_galway_chunk_0668
import Theorems.Thm_Brocard_berndt_galway_chunk_0669
import Theorems.Thm_Brocard_berndt_galway_chunk_0670
import Theorems.Thm_Brocard_berndt_galway_chunk_0671
import Theorems.Thm_Brocard_berndt_galway_chunk_0672
import Theorems.Thm_Brocard_berndt_galway_chunk_0673
import Theorems.Thm_Brocard_berndt_galway_chunk_0674
import Theorems.Thm_Brocard_berndt_galway_chunk_0675
import Theorems.Thm_Brocard_berndt_galway_chunk_0676
import Theorems.Thm_Brocard_berndt_galway_chunk_0677
import Theorems.Thm_Brocard_berndt_galway_chunk_0678
import Theorems.Thm_Brocard_berndt_galway_chunk_0679
import Theorems.Thm_Brocard_berndt_galway_chunk_0680
import Theorems.Thm_Brocard_berndt_galway_chunk_0681
import Theorems.Thm_Brocard_berndt_galway_chunk_0682
import Theorems.Thm_Brocard_berndt_galway_chunk_0683
import Theorems.Thm_Brocard_berndt_galway_chunk_0684
import Theorems.Thm_Brocard_berndt_galway_chunk_0685
import Theorems.Thm_Brocard_berndt_galway_chunk_0686
import Theorems.Thm_Brocard_berndt_galway_chunk_0687
import Theorems.Thm_Brocard_berndt_galway_chunk_0688
import Theorems.Thm_Brocard_berndt_galway_chunk_0689
import Theorems.Thm_Brocard_berndt_galway_chunk_0690
import Theorems.Thm_Brocard_berndt_galway_chunk_0691
import Theorems.Thm_Brocard_berndt_galway_chunk_0692
import Theorems.Thm_Brocard_berndt_galway_chunk_0693
import Theorems.Thm_Brocard_berndt_galway_chunk_0694
import Theorems.Thm_Brocard_berndt_galway_chunk_0695
import Theorems.Thm_Brocard_berndt_galway_chunk_0696
import Theorems.Thm_Brocard_berndt_galway_chunk_0697

theorem solution (n m : ℕ) (h1 : 116906474 ≤ n) (h2 : n < 125359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 121223021 with hs0 | hs0
  · -- n < 121223021
    rcases Nat.lt_or_ge n 119064748 with hs1 | hs1
    · -- n < 119064748
      rcases Nat.lt_or_ge n 117985611 with hs2 | hs2
      · -- n < 117985611
        rcases Nat.lt_or_ge n 117446043 with hs3 | hs3
        · -- n < 117446043
          rcases Nat.lt_or_ge n 117266187 with hs4 | hs4
          · -- n < 117266187
            rcases Nat.lt_or_ge n 117086330 with hs5 | hs5
            · -- n < 117086330
              exact Brocard.berndt_galway_chunk_0651 n m (by omega) (by omega) h
            · -- n >= 117086330
              exact Brocard.berndt_galway_chunk_0652 n m (by omega) (by omega) h
          · -- n >= 117266187
            exact Brocard.berndt_galway_chunk_0653 n m (by omega) (by omega) h
        · -- n >= 117446043
          rcases Nat.lt_or_ge n 117805755 with hs4 | hs4
          · -- n < 117805755
            rcases Nat.lt_or_ge n 117625899 with hs5 | hs5
            · -- n < 117625899
              exact Brocard.berndt_galway_chunk_0654 n m (by omega) (by omega) h
            · -- n >= 117625899
              exact Brocard.berndt_galway_chunk_0655 n m (by omega) (by omega) h
          · -- n >= 117805755
            exact Brocard.berndt_galway_chunk_0656 n m (by omega) (by omega) h
      · -- n >= 117985611
        rcases Nat.lt_or_ge n 118525179 with hs3 | hs3
        · -- n < 118525179
          rcases Nat.lt_or_ge n 118345323 with hs4 | hs4
          · -- n < 118345323
            rcases Nat.lt_or_ge n 118165467 with hs5 | hs5
            · -- n < 118165467
              exact Brocard.berndt_galway_chunk_0657 n m (by omega) (by omega) h
            · -- n >= 118165467
              exact Brocard.berndt_galway_chunk_0658 n m (by omega) (by omega) h
          · -- n >= 118345323
            exact Brocard.berndt_galway_chunk_0659 n m (by omega) (by omega) h
        · -- n >= 118525179
          rcases Nat.lt_or_ge n 118884892 with hs4 | hs4
          · -- n < 118884892
            rcases Nat.lt_or_ge n 118705035 with hs5 | hs5
            · -- n < 118705035
              exact Brocard.berndt_galway_chunk_0660 n m (by omega) (by omega) h
            · -- n >= 118705035
              exact Brocard.berndt_galway_chunk_0661 n m (by omega) (by omega) h
          · -- n >= 118884892
            exact Brocard.berndt_galway_chunk_0662 n m (by omega) (by omega) h
    · -- n >= 119064748
      rcases Nat.lt_or_ge n 120143884 with hs2 | hs2
      · -- n < 120143884
        rcases Nat.lt_or_ge n 119604316 with hs3 | hs3
        · -- n < 119604316
          rcases Nat.lt_or_ge n 119424460 with hs4 | hs4
          · -- n < 119424460
            rcases Nat.lt_or_ge n 119244604 with hs5 | hs5
            · -- n < 119244604
              exact Brocard.berndt_galway_chunk_0663 n m (by omega) (by omega) h
            · -- n >= 119244604
              exact Brocard.berndt_galway_chunk_0664 n m (by omega) (by omega) h
          · -- n >= 119424460
            exact Brocard.berndt_galway_chunk_0665 n m (by omega) (by omega) h
        · -- n >= 119604316
          rcases Nat.lt_or_ge n 119964028 with hs4 | hs4
          · -- n < 119964028
            rcases Nat.lt_or_ge n 119784172 with hs5 | hs5
            · -- n < 119784172
              exact Brocard.berndt_galway_chunk_0666 n m (by omega) (by omega) h
            · -- n >= 119784172
              exact Brocard.berndt_galway_chunk_0667 n m (by omega) (by omega) h
          · -- n >= 119964028
            exact Brocard.berndt_galway_chunk_0668 n m (by omega) (by omega) h
      · -- n >= 120143884
        rcases Nat.lt_or_ge n 120683453 with hs3 | hs3
        · -- n < 120683453
          rcases Nat.lt_or_ge n 120503597 with hs4 | hs4
          · -- n < 120503597
            rcases Nat.lt_or_ge n 120323741 with hs5 | hs5
            · -- n < 120323741
              exact Brocard.berndt_galway_chunk_0669 n m (by omega) (by omega) h
            · -- n >= 120323741
              exact Brocard.berndt_galway_chunk_0670 n m (by omega) (by omega) h
          · -- n >= 120503597
            exact Brocard.berndt_galway_chunk_0671 n m (by omega) (by omega) h
        · -- n >= 120683453
          rcases Nat.lt_or_ge n 121043165 with hs4 | hs4
          · -- n < 121043165
            rcases Nat.lt_or_ge n 120863309 with hs5 | hs5
            · -- n < 120863309
              exact Brocard.berndt_galway_chunk_0672 n m (by omega) (by omega) h
            · -- n >= 120863309
              exact Brocard.berndt_galway_chunk_0673 n m (by omega) (by omega) h
          · -- n >= 121043165
            exact Brocard.berndt_galway_chunk_0674 n m (by omega) (by omega) h
  · -- n >= 121223021
    rcases Nat.lt_or_ge n 123381294 with hs1 | hs1
    · -- n < 123381294
      rcases Nat.lt_or_ge n 122302158 with hs2 | hs2
      · -- n < 122302158
        rcases Nat.lt_or_ge n 121762589 with hs3 | hs3
        · -- n < 121762589
          rcases Nat.lt_or_ge n 121582733 with hs4 | hs4
          · -- n < 121582733
            rcases Nat.lt_or_ge n 121402877 with hs5 | hs5
            · -- n < 121402877
              exact Brocard.berndt_galway_chunk_0675 n m (by omega) (by omega) h
            · -- n >= 121402877
              exact Brocard.berndt_galway_chunk_0676 n m (by omega) (by omega) h
          · -- n >= 121582733
            exact Brocard.berndt_galway_chunk_0677 n m (by omega) (by omega) h
        · -- n >= 121762589
          rcases Nat.lt_or_ge n 122122302 with hs4 | hs4
          · -- n < 122122302
            rcases Nat.lt_or_ge n 121942446 with hs5 | hs5
            · -- n < 121942446
              exact Brocard.berndt_galway_chunk_0678 n m (by omega) (by omega) h
            · -- n >= 121942446
              exact Brocard.berndt_galway_chunk_0679 n m (by omega) (by omega) h
          · -- n >= 122122302
            exact Brocard.berndt_galway_chunk_0680 n m (by omega) (by omega) h
      · -- n >= 122302158
        rcases Nat.lt_or_ge n 122841726 with hs3 | hs3
        · -- n < 122841726
          rcases Nat.lt_or_ge n 122661870 with hs4 | hs4
          · -- n < 122661870
            rcases Nat.lt_or_ge n 122482014 with hs5 | hs5
            · -- n < 122482014
              exact Brocard.berndt_galway_chunk_0681 n m (by omega) (by omega) h
            · -- n >= 122482014
              exact Brocard.berndt_galway_chunk_0682 n m (by omega) (by omega) h
          · -- n >= 122661870
            exact Brocard.berndt_galway_chunk_0683 n m (by omega) (by omega) h
        · -- n >= 122841726
          rcases Nat.lt_or_ge n 123201438 with hs4 | hs4
          · -- n < 123201438
            rcases Nat.lt_or_ge n 123021582 with hs5 | hs5
            · -- n < 123021582
              exact Brocard.berndt_galway_chunk_0684 n m (by omega) (by omega) h
            · -- n >= 123021582
              exact Brocard.berndt_galway_chunk_0685 n m (by omega) (by omega) h
          · -- n >= 123201438
            exact Brocard.berndt_galway_chunk_0686 n m (by omega) (by omega) h
    · -- n >= 123381294
      rcases Nat.lt_or_ge n 124460431 with hs2 | hs2
      · -- n < 124460431
        rcases Nat.lt_or_ge n 123920863 with hs3 | hs3
        · -- n < 123920863
          rcases Nat.lt_or_ge n 123741007 with hs4 | hs4
          · -- n < 123741007
            rcases Nat.lt_or_ge n 123561151 with hs5 | hs5
            · -- n < 123561151
              exact Brocard.berndt_galway_chunk_0687 n m (by omega) (by omega) h
            · -- n >= 123561151
              exact Brocard.berndt_galway_chunk_0688 n m (by omega) (by omega) h
          · -- n >= 123741007
            exact Brocard.berndt_galway_chunk_0689 n m (by omega) (by omega) h
        · -- n >= 123920863
          rcases Nat.lt_or_ge n 124280575 with hs4 | hs4
          · -- n < 124280575
            rcases Nat.lt_or_ge n 124100719 with hs5 | hs5
            · -- n < 124100719
              exact Brocard.berndt_galway_chunk_0690 n m (by omega) (by omega) h
            · -- n >= 124100719
              exact Brocard.berndt_galway_chunk_0691 n m (by omega) (by omega) h
          · -- n >= 124280575
            exact Brocard.berndt_galway_chunk_0692 n m (by omega) (by omega) h
      · -- n >= 124460431
        rcases Nat.lt_or_ge n 125000000 with hs3 | hs3
        · -- n < 125000000
          rcases Nat.lt_or_ge n 124820143 with hs4 | hs4
          · -- n < 124820143
            rcases Nat.lt_or_ge n 124640287 with hs5 | hs5
            · -- n < 124640287
              exact Brocard.berndt_galway_chunk_0693 n m (by omega) (by omega) h
            · -- n >= 124640287
              exact Brocard.berndt_galway_chunk_0694 n m (by omega) (by omega) h
          · -- n >= 124820143
            exact Brocard.berndt_galway_chunk_0695 n m (by omega) (by omega) h
        · -- n >= 125000000
          rcases Nat.lt_or_ge n 125179856 with hs4 | hs4
          · -- n < 125179856
            exact Brocard.berndt_galway_chunk_0696 n m (by omega) (by omega) h
          · -- n >= 125179856
            exact Brocard.berndt_galway_chunk_0697 n m (by omega) (by omega) h
