-- Prove2me | solution 1 for Brocard.berndt_galway_group_084
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:07:58.23798+00:00
-- url     : https://prove2.me/submissions/dfbfc389-0c8c-4555-97eb-6ccd414e3e49

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_3847
import Theorems.Thm_Brocard_berndt_galway_chunk_3848
import Theorems.Thm_Brocard_berndt_galway_chunk_3849
import Theorems.Thm_Brocard_berndt_galway_chunk_3850
import Theorems.Thm_Brocard_berndt_galway_chunk_3851
import Theorems.Thm_Brocard_berndt_galway_chunk_3852
import Theorems.Thm_Brocard_berndt_galway_chunk_3853
import Theorems.Thm_Brocard_berndt_galway_chunk_3854
import Theorems.Thm_Brocard_berndt_galway_chunk_3855
import Theorems.Thm_Brocard_berndt_galway_chunk_3856
import Theorems.Thm_Brocard_berndt_galway_chunk_3857
import Theorems.Thm_Brocard_berndt_galway_chunk_3858
import Theorems.Thm_Brocard_berndt_galway_chunk_3859
import Theorems.Thm_Brocard_berndt_galway_chunk_3860
import Theorems.Thm_Brocard_berndt_galway_chunk_3861
import Theorems.Thm_Brocard_berndt_galway_chunk_3862
import Theorems.Thm_Brocard_berndt_galway_chunk_3863
import Theorems.Thm_Brocard_berndt_galway_chunk_3864
import Theorems.Thm_Brocard_berndt_galway_chunk_3865
import Theorems.Thm_Brocard_berndt_galway_chunk_3866
import Theorems.Thm_Brocard_berndt_galway_chunk_3867
import Theorems.Thm_Brocard_berndt_galway_chunk_3868
import Theorems.Thm_Brocard_berndt_galway_chunk_3869
import Theorems.Thm_Brocard_berndt_galway_chunk_3870
import Theorems.Thm_Brocard_berndt_galway_chunk_3871
import Theorems.Thm_Brocard_berndt_galway_chunk_3872
import Theorems.Thm_Brocard_berndt_galway_chunk_3873
import Theorems.Thm_Brocard_berndt_galway_chunk_3874
import Theorems.Thm_Brocard_berndt_galway_chunk_3875
import Theorems.Thm_Brocard_berndt_galway_chunk_3876
import Theorems.Thm_Brocard_berndt_galway_chunk_3877
import Theorems.Thm_Brocard_berndt_galway_chunk_3878
import Theorems.Thm_Brocard_berndt_galway_chunk_3879
import Theorems.Thm_Brocard_berndt_galway_chunk_3880
import Theorems.Thm_Brocard_berndt_galway_chunk_3881
import Theorems.Thm_Brocard_berndt_galway_chunk_3882
import Theorems.Thm_Brocard_berndt_galway_chunk_3883
import Theorems.Thm_Brocard_berndt_galway_chunk_3884
import Theorems.Thm_Brocard_berndt_galway_chunk_3885
import Theorems.Thm_Brocard_berndt_galway_chunk_3886
import Theorems.Thm_Brocard_berndt_galway_chunk_3887
import Theorems.Thm_Brocard_berndt_galway_chunk_3888
import Theorems.Thm_Brocard_berndt_galway_chunk_3889
import Theorems.Thm_Brocard_berndt_galway_chunk_3890
import Theorems.Thm_Brocard_berndt_galway_chunk_3891
import Theorems.Thm_Brocard_berndt_galway_chunk_3892

theorem solution (n m : ℕ) (h1 : 691726618 ≤ n) (h2 : n < 700000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 695863309 with hs0 | hs0
  · -- n < 695863309
    rcases Nat.lt_or_ge n 693884892 with hs1 | hs1
    · -- n < 693884892
      rcases Nat.lt_or_ge n 692805755 with hs2 | hs2
      · -- n < 692805755
        rcases Nat.lt_or_ge n 692266187 with hs3 | hs3
        · -- n < 692266187
          rcases Nat.lt_or_ge n 692086330 with hs4 | hs4
          · -- n < 692086330
            rcases Nat.lt_or_ge n 691906474 with hs5 | hs5
            · -- n < 691906474
              exact Brocard.berndt_galway_chunk_3847 n m (by omega) (by omega) h
            · -- n >= 691906474
              exact Brocard.berndt_galway_chunk_3848 n m (by omega) (by omega) h
          · -- n >= 692086330
            exact Brocard.berndt_galway_chunk_3849 n m (by omega) (by omega) h
        · -- n >= 692266187
          rcases Nat.lt_or_ge n 692625899 with hs4 | hs4
          · -- n < 692625899
            rcases Nat.lt_or_ge n 692446043 with hs5 | hs5
            · -- n < 692446043
              exact Brocard.berndt_galway_chunk_3850 n m (by omega) (by omega) h
            · -- n >= 692446043
              exact Brocard.berndt_galway_chunk_3851 n m (by omega) (by omega) h
          · -- n >= 692625899
            exact Brocard.berndt_galway_chunk_3852 n m (by omega) (by omega) h
      · -- n >= 692805755
        rcases Nat.lt_or_ge n 693345323 with hs3 | hs3
        · -- n < 693345323
          rcases Nat.lt_or_ge n 693165467 with hs4 | hs4
          · -- n < 693165467
            rcases Nat.lt_or_ge n 692985611 with hs5 | hs5
            · -- n < 692985611
              exact Brocard.berndt_galway_chunk_3853 n m (by omega) (by omega) h
            · -- n >= 692985611
              exact Brocard.berndt_galway_chunk_3854 n m (by omega) (by omega) h
          · -- n >= 693165467
            exact Brocard.berndt_galway_chunk_3855 n m (by omega) (by omega) h
        · -- n >= 693345323
          rcases Nat.lt_or_ge n 693705035 with hs4 | hs4
          · -- n < 693705035
            rcases Nat.lt_or_ge n 693525179 with hs5 | hs5
            · -- n < 693525179
              exact Brocard.berndt_galway_chunk_3856 n m (by omega) (by omega) h
            · -- n >= 693525179
              exact Brocard.berndt_galway_chunk_3857 n m (by omega) (by omega) h
          · -- n >= 693705035
            exact Brocard.berndt_galway_chunk_3858 n m (by omega) (by omega) h
    · -- n >= 693884892
      rcases Nat.lt_or_ge n 694964028 with hs2 | hs2
      · -- n < 694964028
        rcases Nat.lt_or_ge n 694424460 with hs3 | hs3
        · -- n < 694424460
          rcases Nat.lt_or_ge n 694244604 with hs4 | hs4
          · -- n < 694244604
            rcases Nat.lt_or_ge n 694064748 with hs5 | hs5
            · -- n < 694064748
              exact Brocard.berndt_galway_chunk_3859 n m (by omega) (by omega) h
            · -- n >= 694064748
              exact Brocard.berndt_galway_chunk_3860 n m (by omega) (by omega) h
          · -- n >= 694244604
            exact Brocard.berndt_galway_chunk_3861 n m (by omega) (by omega) h
        · -- n >= 694424460
          rcases Nat.lt_or_ge n 694784172 with hs4 | hs4
          · -- n < 694784172
            rcases Nat.lt_or_ge n 694604316 with hs5 | hs5
            · -- n < 694604316
              exact Brocard.berndt_galway_chunk_3862 n m (by omega) (by omega) h
            · -- n >= 694604316
              exact Brocard.berndt_galway_chunk_3863 n m (by omega) (by omega) h
          · -- n >= 694784172
            exact Brocard.berndt_galway_chunk_3864 n m (by omega) (by omega) h
      · -- n >= 694964028
        rcases Nat.lt_or_ge n 695503597 with hs3 | hs3
        · -- n < 695503597
          rcases Nat.lt_or_ge n 695323741 with hs4 | hs4
          · -- n < 695323741
            rcases Nat.lt_or_ge n 695143884 with hs5 | hs5
            · -- n < 695143884
              exact Brocard.berndt_galway_chunk_3865 n m (by omega) (by omega) h
            · -- n >= 695143884
              exact Brocard.berndt_galway_chunk_3866 n m (by omega) (by omega) h
          · -- n >= 695323741
            exact Brocard.berndt_galway_chunk_3867 n m (by omega) (by omega) h
        · -- n >= 695503597
          rcases Nat.lt_or_ge n 695683453 with hs4 | hs4
          · -- n < 695683453
            exact Brocard.berndt_galway_chunk_3868 n m (by omega) (by omega) h
          · -- n >= 695683453
            exact Brocard.berndt_galway_chunk_3869 n m (by omega) (by omega) h
  · -- n >= 695863309
    rcases Nat.lt_or_ge n 698021582 with hs1 | hs1
    · -- n < 698021582
      rcases Nat.lt_or_ge n 696942446 with hs2 | hs2
      · -- n < 696942446
        rcases Nat.lt_or_ge n 696402877 with hs3 | hs3
        · -- n < 696402877
          rcases Nat.lt_or_ge n 696223021 with hs4 | hs4
          · -- n < 696223021
            rcases Nat.lt_or_ge n 696043165 with hs5 | hs5
            · -- n < 696043165
              exact Brocard.berndt_galway_chunk_3870 n m (by omega) (by omega) h
            · -- n >= 696043165
              exact Brocard.berndt_galway_chunk_3871 n m (by omega) (by omega) h
          · -- n >= 696223021
            exact Brocard.berndt_galway_chunk_3872 n m (by omega) (by omega) h
        · -- n >= 696402877
          rcases Nat.lt_or_ge n 696762589 with hs4 | hs4
          · -- n < 696762589
            rcases Nat.lt_or_ge n 696582733 with hs5 | hs5
            · -- n < 696582733
              exact Brocard.berndt_galway_chunk_3873 n m (by omega) (by omega) h
            · -- n >= 696582733
              exact Brocard.berndt_galway_chunk_3874 n m (by omega) (by omega) h
          · -- n >= 696762589
            exact Brocard.berndt_galway_chunk_3875 n m (by omega) (by omega) h
      · -- n >= 696942446
        rcases Nat.lt_or_ge n 697482014 with hs3 | hs3
        · -- n < 697482014
          rcases Nat.lt_or_ge n 697302158 with hs4 | hs4
          · -- n < 697302158
            rcases Nat.lt_or_ge n 697122302 with hs5 | hs5
            · -- n < 697122302
              exact Brocard.berndt_galway_chunk_3876 n m (by omega) (by omega) h
            · -- n >= 697122302
              exact Brocard.berndt_galway_chunk_3877 n m (by omega) (by omega) h
          · -- n >= 697302158
            exact Brocard.berndt_galway_chunk_3878 n m (by omega) (by omega) h
        · -- n >= 697482014
          rcases Nat.lt_or_ge n 697841726 with hs4 | hs4
          · -- n < 697841726
            rcases Nat.lt_or_ge n 697661870 with hs5 | hs5
            · -- n < 697661870
              exact Brocard.berndt_galway_chunk_3879 n m (by omega) (by omega) h
            · -- n >= 697661870
              exact Brocard.berndt_galway_chunk_3880 n m (by omega) (by omega) h
          · -- n >= 697841726
            exact Brocard.berndt_galway_chunk_3881 n m (by omega) (by omega) h
    · -- n >= 698021582
      rcases Nat.lt_or_ge n 699100719 with hs2 | hs2
      · -- n < 699100719
        rcases Nat.lt_or_ge n 698561151 with hs3 | hs3
        · -- n < 698561151
          rcases Nat.lt_or_ge n 698381294 with hs4 | hs4
          · -- n < 698381294
            rcases Nat.lt_or_ge n 698201438 with hs5 | hs5
            · -- n < 698201438
              exact Brocard.berndt_galway_chunk_3882 n m (by omega) (by omega) h
            · -- n >= 698201438
              exact Brocard.berndt_galway_chunk_3883 n m (by omega) (by omega) h
          · -- n >= 698381294
            exact Brocard.berndt_galway_chunk_3884 n m (by omega) (by omega) h
        · -- n >= 698561151
          rcases Nat.lt_or_ge n 698920863 with hs4 | hs4
          · -- n < 698920863
            rcases Nat.lt_or_ge n 698741007 with hs5 | hs5
            · -- n < 698741007
              exact Brocard.berndt_galway_chunk_3885 n m (by omega) (by omega) h
            · -- n >= 698741007
              exact Brocard.berndt_galway_chunk_3886 n m (by omega) (by omega) h
          · -- n >= 698920863
            exact Brocard.berndt_galway_chunk_3887 n m (by omega) (by omega) h
      · -- n >= 699100719
        rcases Nat.lt_or_ge n 699640287 with hs3 | hs3
        · -- n < 699640287
          rcases Nat.lt_or_ge n 699460431 with hs4 | hs4
          · -- n < 699460431
            rcases Nat.lt_or_ge n 699280575 with hs5 | hs5
            · -- n < 699280575
              exact Brocard.berndt_galway_chunk_3888 n m (by omega) (by omega) h
            · -- n >= 699280575
              exact Brocard.berndt_galway_chunk_3889 n m (by omega) (by omega) h
          · -- n >= 699460431
            exact Brocard.berndt_galway_chunk_3890 n m (by omega) (by omega) h
        · -- n >= 699640287
          rcases Nat.lt_or_ge n 699820143 with hs4 | hs4
          · -- n < 699820143
            exact Brocard.berndt_galway_chunk_3891 n m (by omega) (by omega) h
          · -- n >= 699820143
            exact Brocard.berndt_galway_chunk_3892 n m (by omega) (by omega) h
