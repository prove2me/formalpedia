-- Prove2me | solution 1 for Brocard.berndt_galway_group_102
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:42:00.22975+00:00
-- url     : https://prove2.me/submissions/eeed900f-8a5b-478c-88c5-25c4a497d89b

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_4683
import Theorems.Thm_Brocard_berndt_galway_chunk_4684
import Theorems.Thm_Brocard_berndt_galway_chunk_4685
import Theorems.Thm_Brocard_berndt_galway_chunk_4686
import Theorems.Thm_Brocard_berndt_galway_chunk_4687
import Theorems.Thm_Brocard_berndt_galway_chunk_4688
import Theorems.Thm_Brocard_berndt_galway_chunk_4689
import Theorems.Thm_Brocard_berndt_galway_chunk_4690
import Theorems.Thm_Brocard_berndt_galway_chunk_4691
import Theorems.Thm_Brocard_berndt_galway_chunk_4692
import Theorems.Thm_Brocard_berndt_galway_chunk_4693
import Theorems.Thm_Brocard_berndt_galway_chunk_4694
import Theorems.Thm_Brocard_berndt_galway_chunk_4695
import Theorems.Thm_Brocard_berndt_galway_chunk_4696
import Theorems.Thm_Brocard_berndt_galway_chunk_4697
import Theorems.Thm_Brocard_berndt_galway_chunk_4698
import Theorems.Thm_Brocard_berndt_galway_chunk_4699
import Theorems.Thm_Brocard_berndt_galway_chunk_4700
import Theorems.Thm_Brocard_berndt_galway_chunk_4701
import Theorems.Thm_Brocard_berndt_galway_chunk_4702
import Theorems.Thm_Brocard_berndt_galway_chunk_4703
import Theorems.Thm_Brocard_berndt_galway_chunk_4704
import Theorems.Thm_Brocard_berndt_galway_chunk_4705
import Theorems.Thm_Brocard_berndt_galway_chunk_4706
import Theorems.Thm_Brocard_berndt_galway_chunk_4707
import Theorems.Thm_Brocard_berndt_galway_chunk_4708
import Theorems.Thm_Brocard_berndt_galway_chunk_4709
import Theorems.Thm_Brocard_berndt_galway_chunk_4710
import Theorems.Thm_Brocard_berndt_galway_chunk_4711
import Theorems.Thm_Brocard_berndt_galway_chunk_4712
import Theorems.Thm_Brocard_berndt_galway_chunk_4713
import Theorems.Thm_Brocard_berndt_galway_chunk_4714
import Theorems.Thm_Brocard_berndt_galway_chunk_4715
import Theorems.Thm_Brocard_berndt_galway_chunk_4716
import Theorems.Thm_Brocard_berndt_galway_chunk_4717
import Theorems.Thm_Brocard_berndt_galway_chunk_4718
import Theorems.Thm_Brocard_berndt_galway_chunk_4719
import Theorems.Thm_Brocard_berndt_galway_chunk_4720
import Theorems.Thm_Brocard_berndt_galway_chunk_4721
import Theorems.Thm_Brocard_berndt_galway_chunk_4722
import Theorems.Thm_Brocard_berndt_galway_chunk_4723
import Theorems.Thm_Brocard_berndt_galway_chunk_4724
import Theorems.Thm_Brocard_berndt_galway_chunk_4725
import Theorems.Thm_Brocard_berndt_galway_chunk_4726
import Theorems.Thm_Brocard_berndt_galway_chunk_4727
import Theorems.Thm_Brocard_berndt_galway_chunk_4728

theorem solution (n m : ℕ) (h1 : 842086330 ≤ n) (h2 : n < 850359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 846223021 with hs0 | hs0
  · -- n < 846223021
    rcases Nat.lt_or_ge n 844244604 with hs1 | hs1
    · -- n < 844244604
      rcases Nat.lt_or_ge n 843165467 with hs2 | hs2
      · -- n < 843165467
        rcases Nat.lt_or_ge n 842625899 with hs3 | hs3
        · -- n < 842625899
          rcases Nat.lt_or_ge n 842446043 with hs4 | hs4
          · -- n < 842446043
            rcases Nat.lt_or_ge n 842266187 with hs5 | hs5
            · -- n < 842266187
              exact Brocard.berndt_galway_chunk_4683 n m (by omega) (by omega) h
            · -- n >= 842266187
              exact Brocard.berndt_galway_chunk_4684 n m (by omega) (by omega) h
          · -- n >= 842446043
            exact Brocard.berndt_galway_chunk_4685 n m (by omega) (by omega) h
        · -- n >= 842625899
          rcases Nat.lt_or_ge n 842985611 with hs4 | hs4
          · -- n < 842985611
            rcases Nat.lt_or_ge n 842805755 with hs5 | hs5
            · -- n < 842805755
              exact Brocard.berndt_galway_chunk_4686 n m (by omega) (by omega) h
            · -- n >= 842805755
              exact Brocard.berndt_galway_chunk_4687 n m (by omega) (by omega) h
          · -- n >= 842985611
            exact Brocard.berndt_galway_chunk_4688 n m (by omega) (by omega) h
      · -- n >= 843165467
        rcases Nat.lt_or_ge n 843705035 with hs3 | hs3
        · -- n < 843705035
          rcases Nat.lt_or_ge n 843525179 with hs4 | hs4
          · -- n < 843525179
            rcases Nat.lt_or_ge n 843345323 with hs5 | hs5
            · -- n < 843345323
              exact Brocard.berndt_galway_chunk_4689 n m (by omega) (by omega) h
            · -- n >= 843345323
              exact Brocard.berndt_galway_chunk_4690 n m (by omega) (by omega) h
          · -- n >= 843525179
            exact Brocard.berndt_galway_chunk_4691 n m (by omega) (by omega) h
        · -- n >= 843705035
          rcases Nat.lt_or_ge n 844064748 with hs4 | hs4
          · -- n < 844064748
            rcases Nat.lt_or_ge n 843884892 with hs5 | hs5
            · -- n < 843884892
              exact Brocard.berndt_galway_chunk_4692 n m (by omega) (by omega) h
            · -- n >= 843884892
              exact Brocard.berndt_galway_chunk_4693 n m (by omega) (by omega) h
          · -- n >= 844064748
            exact Brocard.berndt_galway_chunk_4694 n m (by omega) (by omega) h
    · -- n >= 844244604
      rcases Nat.lt_or_ge n 845323741 with hs2 | hs2
      · -- n < 845323741
        rcases Nat.lt_or_ge n 844784172 with hs3 | hs3
        · -- n < 844784172
          rcases Nat.lt_or_ge n 844604316 with hs4 | hs4
          · -- n < 844604316
            rcases Nat.lt_or_ge n 844424460 with hs5 | hs5
            · -- n < 844424460
              exact Brocard.berndt_galway_chunk_4695 n m (by omega) (by omega) h
            · -- n >= 844424460
              exact Brocard.berndt_galway_chunk_4696 n m (by omega) (by omega) h
          · -- n >= 844604316
            exact Brocard.berndt_galway_chunk_4697 n m (by omega) (by omega) h
        · -- n >= 844784172
          rcases Nat.lt_or_ge n 845143884 with hs4 | hs4
          · -- n < 845143884
            rcases Nat.lt_or_ge n 844964028 with hs5 | hs5
            · -- n < 844964028
              exact Brocard.berndt_galway_chunk_4698 n m (by omega) (by omega) h
            · -- n >= 844964028
              exact Brocard.berndt_galway_chunk_4699 n m (by omega) (by omega) h
          · -- n >= 845143884
            exact Brocard.berndt_galway_chunk_4700 n m (by omega) (by omega) h
      · -- n >= 845323741
        rcases Nat.lt_or_ge n 845863309 with hs3 | hs3
        · -- n < 845863309
          rcases Nat.lt_or_ge n 845683453 with hs4 | hs4
          · -- n < 845683453
            rcases Nat.lt_or_ge n 845503597 with hs5 | hs5
            · -- n < 845503597
              exact Brocard.berndt_galway_chunk_4701 n m (by omega) (by omega) h
            · -- n >= 845503597
              exact Brocard.berndt_galway_chunk_4702 n m (by omega) (by omega) h
          · -- n >= 845683453
            exact Brocard.berndt_galway_chunk_4703 n m (by omega) (by omega) h
        · -- n >= 845863309
          rcases Nat.lt_or_ge n 846043165 with hs4 | hs4
          · -- n < 846043165
            exact Brocard.berndt_galway_chunk_4704 n m (by omega) (by omega) h
          · -- n >= 846043165
            exact Brocard.berndt_galway_chunk_4705 n m (by omega) (by omega) h
  · -- n >= 846223021
    rcases Nat.lt_or_ge n 848381294 with hs1 | hs1
    · -- n < 848381294
      rcases Nat.lt_or_ge n 847302158 with hs2 | hs2
      · -- n < 847302158
        rcases Nat.lt_or_ge n 846762589 with hs3 | hs3
        · -- n < 846762589
          rcases Nat.lt_or_ge n 846582733 with hs4 | hs4
          · -- n < 846582733
            rcases Nat.lt_or_ge n 846402877 with hs5 | hs5
            · -- n < 846402877
              exact Brocard.berndt_galway_chunk_4706 n m (by omega) (by omega) h
            · -- n >= 846402877
              exact Brocard.berndt_galway_chunk_4707 n m (by omega) (by omega) h
          · -- n >= 846582733
            exact Brocard.berndt_galway_chunk_4708 n m (by omega) (by omega) h
        · -- n >= 846762589
          rcases Nat.lt_or_ge n 847122302 with hs4 | hs4
          · -- n < 847122302
            rcases Nat.lt_or_ge n 846942446 with hs5 | hs5
            · -- n < 846942446
              exact Brocard.berndt_galway_chunk_4709 n m (by omega) (by omega) h
            · -- n >= 846942446
              exact Brocard.berndt_galway_chunk_4710 n m (by omega) (by omega) h
          · -- n >= 847122302
            exact Brocard.berndt_galway_chunk_4711 n m (by omega) (by omega) h
      · -- n >= 847302158
        rcases Nat.lt_or_ge n 847841726 with hs3 | hs3
        · -- n < 847841726
          rcases Nat.lt_or_ge n 847661870 with hs4 | hs4
          · -- n < 847661870
            rcases Nat.lt_or_ge n 847482014 with hs5 | hs5
            · -- n < 847482014
              exact Brocard.berndt_galway_chunk_4712 n m (by omega) (by omega) h
            · -- n >= 847482014
              exact Brocard.berndt_galway_chunk_4713 n m (by omega) (by omega) h
          · -- n >= 847661870
            exact Brocard.berndt_galway_chunk_4714 n m (by omega) (by omega) h
        · -- n >= 847841726
          rcases Nat.lt_or_ge n 848201438 with hs4 | hs4
          · -- n < 848201438
            rcases Nat.lt_or_ge n 848021582 with hs5 | hs5
            · -- n < 848021582
              exact Brocard.berndt_galway_chunk_4715 n m (by omega) (by omega) h
            · -- n >= 848021582
              exact Brocard.berndt_galway_chunk_4716 n m (by omega) (by omega) h
          · -- n >= 848201438
            exact Brocard.berndt_galway_chunk_4717 n m (by omega) (by omega) h
    · -- n >= 848381294
      rcases Nat.lt_or_ge n 849460431 with hs2 | hs2
      · -- n < 849460431
        rcases Nat.lt_or_ge n 848920863 with hs3 | hs3
        · -- n < 848920863
          rcases Nat.lt_or_ge n 848741007 with hs4 | hs4
          · -- n < 848741007
            rcases Nat.lt_or_ge n 848561151 with hs5 | hs5
            · -- n < 848561151
              exact Brocard.berndt_galway_chunk_4718 n m (by omega) (by omega) h
            · -- n >= 848561151
              exact Brocard.berndt_galway_chunk_4719 n m (by omega) (by omega) h
          · -- n >= 848741007
            exact Brocard.berndt_galway_chunk_4720 n m (by omega) (by omega) h
        · -- n >= 848920863
          rcases Nat.lt_or_ge n 849280575 with hs4 | hs4
          · -- n < 849280575
            rcases Nat.lt_or_ge n 849100719 with hs5 | hs5
            · -- n < 849100719
              exact Brocard.berndt_galway_chunk_4721 n m (by omega) (by omega) h
            · -- n >= 849100719
              exact Brocard.berndt_galway_chunk_4722 n m (by omega) (by omega) h
          · -- n >= 849280575
            exact Brocard.berndt_galway_chunk_4723 n m (by omega) (by omega) h
      · -- n >= 849460431
        rcases Nat.lt_or_ge n 850000000 with hs3 | hs3
        · -- n < 850000000
          rcases Nat.lt_or_ge n 849820143 with hs4 | hs4
          · -- n < 849820143
            rcases Nat.lt_or_ge n 849640287 with hs5 | hs5
            · -- n < 849640287
              exact Brocard.berndt_galway_chunk_4724 n m (by omega) (by omega) h
            · -- n >= 849640287
              exact Brocard.berndt_galway_chunk_4725 n m (by omega) (by omega) h
          · -- n >= 849820143
            exact Brocard.berndt_galway_chunk_4726 n m (by omega) (by omega) h
        · -- n >= 850000000
          rcases Nat.lt_or_ge n 850179856 with hs4 | hs4
          · -- n < 850179856
            exact Brocard.berndt_galway_chunk_4727 n m (by omega) (by omega) h
          · -- n >= 850179856
            exact Brocard.berndt_galway_chunk_4728 n m (by omega) (by omega) h
