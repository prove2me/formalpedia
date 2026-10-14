-- Prove2me | solution 1 for Brocard.berndt_galway_group_021
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:42:57.407299+00:00
-- url     : https://prove2.me/submissions/11724eef-0ebf-413d-9896-71a5724e6266

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_0929
import Theorems.Thm_Brocard_berndt_galway_chunk_0930
import Theorems.Thm_Brocard_berndt_galway_chunk_0931
import Theorems.Thm_Brocard_berndt_galway_chunk_0932
import Theorems.Thm_Brocard_berndt_galway_chunk_0933
import Theorems.Thm_Brocard_berndt_galway_chunk_0934
import Theorems.Thm_Brocard_berndt_galway_chunk_0935
import Theorems.Thm_Brocard_berndt_galway_chunk_0936
import Theorems.Thm_Brocard_berndt_galway_chunk_0937
import Theorems.Thm_Brocard_berndt_galway_chunk_0938
import Theorems.Thm_Brocard_berndt_galway_chunk_0939
import Theorems.Thm_Brocard_berndt_galway_chunk_0940
import Theorems.Thm_Brocard_berndt_galway_chunk_0941
import Theorems.Thm_Brocard_berndt_galway_chunk_0942
import Theorems.Thm_Brocard_berndt_galway_chunk_0943
import Theorems.Thm_Brocard_berndt_galway_chunk_0944
import Theorems.Thm_Brocard_berndt_galway_chunk_0945
import Theorems.Thm_Brocard_berndt_galway_chunk_0946
import Theorems.Thm_Brocard_berndt_galway_chunk_0947
import Theorems.Thm_Brocard_berndt_galway_chunk_0948
import Theorems.Thm_Brocard_berndt_galway_chunk_0949
import Theorems.Thm_Brocard_berndt_galway_chunk_0950
import Theorems.Thm_Brocard_berndt_galway_chunk_0951
import Theorems.Thm_Brocard_berndt_galway_chunk_0952
import Theorems.Thm_Brocard_berndt_galway_chunk_0953
import Theorems.Thm_Brocard_berndt_galway_chunk_0954
import Theorems.Thm_Brocard_berndt_galway_chunk_0955
import Theorems.Thm_Brocard_berndt_galway_chunk_0956
import Theorems.Thm_Brocard_berndt_galway_chunk_0957
import Theorems.Thm_Brocard_berndt_galway_chunk_0958
import Theorems.Thm_Brocard_berndt_galway_chunk_0959
import Theorems.Thm_Brocard_berndt_galway_chunk_0960
import Theorems.Thm_Brocard_berndt_galway_chunk_0961
import Theorems.Thm_Brocard_berndt_galway_chunk_0962
import Theorems.Thm_Brocard_berndt_galway_chunk_0963
import Theorems.Thm_Brocard_berndt_galway_chunk_0964
import Theorems.Thm_Brocard_berndt_galway_chunk_0965
import Theorems.Thm_Brocard_berndt_galway_chunk_0966
import Theorems.Thm_Brocard_berndt_galway_chunk_0967
import Theorems.Thm_Brocard_berndt_galway_chunk_0968
import Theorems.Thm_Brocard_berndt_galway_chunk_0969
import Theorems.Thm_Brocard_berndt_galway_chunk_0970
import Theorems.Thm_Brocard_berndt_galway_chunk_0971
import Theorems.Thm_Brocard_berndt_galway_chunk_0972
import Theorems.Thm_Brocard_berndt_galway_chunk_0973
import Theorems.Thm_Brocard_berndt_galway_chunk_0974

theorem solution (n m : ℕ) (h1 : 166906474 ≤ n) (h2 : n < 175179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 171043165 with hs0 | hs0
  · -- n < 171043165
    rcases Nat.lt_or_ge n 169064748 with hs1 | hs1
    · -- n < 169064748
      rcases Nat.lt_or_ge n 167985611 with hs2 | hs2
      · -- n < 167985611
        rcases Nat.lt_or_ge n 167446043 with hs3 | hs3
        · -- n < 167446043
          rcases Nat.lt_or_ge n 167266187 with hs4 | hs4
          · -- n < 167266187
            rcases Nat.lt_or_ge n 167086330 with hs5 | hs5
            · -- n < 167086330
              exact Brocard.berndt_galway_chunk_0929 n m (by omega) (by omega) h
            · -- n >= 167086330
              exact Brocard.berndt_galway_chunk_0930 n m (by omega) (by omega) h
          · -- n >= 167266187
            exact Brocard.berndt_galway_chunk_0931 n m (by omega) (by omega) h
        · -- n >= 167446043
          rcases Nat.lt_or_ge n 167805755 with hs4 | hs4
          · -- n < 167805755
            rcases Nat.lt_or_ge n 167625899 with hs5 | hs5
            · -- n < 167625899
              exact Brocard.berndt_galway_chunk_0932 n m (by omega) (by omega) h
            · -- n >= 167625899
              exact Brocard.berndt_galway_chunk_0933 n m (by omega) (by omega) h
          · -- n >= 167805755
            exact Brocard.berndt_galway_chunk_0934 n m (by omega) (by omega) h
      · -- n >= 167985611
        rcases Nat.lt_or_ge n 168525179 with hs3 | hs3
        · -- n < 168525179
          rcases Nat.lt_or_ge n 168345323 with hs4 | hs4
          · -- n < 168345323
            rcases Nat.lt_or_ge n 168165467 with hs5 | hs5
            · -- n < 168165467
              exact Brocard.berndt_galway_chunk_0935 n m (by omega) (by omega) h
            · -- n >= 168165467
              exact Brocard.berndt_galway_chunk_0936 n m (by omega) (by omega) h
          · -- n >= 168345323
            exact Brocard.berndt_galway_chunk_0937 n m (by omega) (by omega) h
        · -- n >= 168525179
          rcases Nat.lt_or_ge n 168884892 with hs4 | hs4
          · -- n < 168884892
            rcases Nat.lt_or_ge n 168705035 with hs5 | hs5
            · -- n < 168705035
              exact Brocard.berndt_galway_chunk_0938 n m (by omega) (by omega) h
            · -- n >= 168705035
              exact Brocard.berndt_galway_chunk_0939 n m (by omega) (by omega) h
          · -- n >= 168884892
            exact Brocard.berndt_galway_chunk_0940 n m (by omega) (by omega) h
    · -- n >= 169064748
      rcases Nat.lt_or_ge n 170143884 with hs2 | hs2
      · -- n < 170143884
        rcases Nat.lt_or_ge n 169604316 with hs3 | hs3
        · -- n < 169604316
          rcases Nat.lt_or_ge n 169424460 with hs4 | hs4
          · -- n < 169424460
            rcases Nat.lt_or_ge n 169244604 with hs5 | hs5
            · -- n < 169244604
              exact Brocard.berndt_galway_chunk_0941 n m (by omega) (by omega) h
            · -- n >= 169244604
              exact Brocard.berndt_galway_chunk_0942 n m (by omega) (by omega) h
          · -- n >= 169424460
            exact Brocard.berndt_galway_chunk_0943 n m (by omega) (by omega) h
        · -- n >= 169604316
          rcases Nat.lt_or_ge n 169964028 with hs4 | hs4
          · -- n < 169964028
            rcases Nat.lt_or_ge n 169784172 with hs5 | hs5
            · -- n < 169784172
              exact Brocard.berndt_galway_chunk_0944 n m (by omega) (by omega) h
            · -- n >= 169784172
              exact Brocard.berndt_galway_chunk_0945 n m (by omega) (by omega) h
          · -- n >= 169964028
            exact Brocard.berndt_galway_chunk_0946 n m (by omega) (by omega) h
      · -- n >= 170143884
        rcases Nat.lt_or_ge n 170683453 with hs3 | hs3
        · -- n < 170683453
          rcases Nat.lt_or_ge n 170503597 with hs4 | hs4
          · -- n < 170503597
            rcases Nat.lt_or_ge n 170323741 with hs5 | hs5
            · -- n < 170323741
              exact Brocard.berndt_galway_chunk_0947 n m (by omega) (by omega) h
            · -- n >= 170323741
              exact Brocard.berndt_galway_chunk_0948 n m (by omega) (by omega) h
          · -- n >= 170503597
            exact Brocard.berndt_galway_chunk_0949 n m (by omega) (by omega) h
        · -- n >= 170683453
          rcases Nat.lt_or_ge n 170863309 with hs4 | hs4
          · -- n < 170863309
            exact Brocard.berndt_galway_chunk_0950 n m (by omega) (by omega) h
          · -- n >= 170863309
            exact Brocard.berndt_galway_chunk_0951 n m (by omega) (by omega) h
  · -- n >= 171043165
    rcases Nat.lt_or_ge n 173201438 with hs1 | hs1
    · -- n < 173201438
      rcases Nat.lt_or_ge n 172122302 with hs2 | hs2
      · -- n < 172122302
        rcases Nat.lt_or_ge n 171582733 with hs3 | hs3
        · -- n < 171582733
          rcases Nat.lt_or_ge n 171402877 with hs4 | hs4
          · -- n < 171402877
            rcases Nat.lt_or_ge n 171223021 with hs5 | hs5
            · -- n < 171223021
              exact Brocard.berndt_galway_chunk_0952 n m (by omega) (by omega) h
            · -- n >= 171223021
              exact Brocard.berndt_galway_chunk_0953 n m (by omega) (by omega) h
          · -- n >= 171402877
            exact Brocard.berndt_galway_chunk_0954 n m (by omega) (by omega) h
        · -- n >= 171582733
          rcases Nat.lt_or_ge n 171942446 with hs4 | hs4
          · -- n < 171942446
            rcases Nat.lt_or_ge n 171762589 with hs5 | hs5
            · -- n < 171762589
              exact Brocard.berndt_galway_chunk_0955 n m (by omega) (by omega) h
            · -- n >= 171762589
              exact Brocard.berndt_galway_chunk_0956 n m (by omega) (by omega) h
          · -- n >= 171942446
            exact Brocard.berndt_galway_chunk_0957 n m (by omega) (by omega) h
      · -- n >= 172122302
        rcases Nat.lt_or_ge n 172661870 with hs3 | hs3
        · -- n < 172661870
          rcases Nat.lt_or_ge n 172482014 with hs4 | hs4
          · -- n < 172482014
            rcases Nat.lt_or_ge n 172302158 with hs5 | hs5
            · -- n < 172302158
              exact Brocard.berndt_galway_chunk_0958 n m (by omega) (by omega) h
            · -- n >= 172302158
              exact Brocard.berndt_galway_chunk_0959 n m (by omega) (by omega) h
          · -- n >= 172482014
            exact Brocard.berndt_galway_chunk_0960 n m (by omega) (by omega) h
        · -- n >= 172661870
          rcases Nat.lt_or_ge n 173021582 with hs4 | hs4
          · -- n < 173021582
            rcases Nat.lt_or_ge n 172841726 with hs5 | hs5
            · -- n < 172841726
              exact Brocard.berndt_galway_chunk_0961 n m (by omega) (by omega) h
            · -- n >= 172841726
              exact Brocard.berndt_galway_chunk_0962 n m (by omega) (by omega) h
          · -- n >= 173021582
            exact Brocard.berndt_galway_chunk_0963 n m (by omega) (by omega) h
    · -- n >= 173201438
      rcases Nat.lt_or_ge n 174280575 with hs2 | hs2
      · -- n < 174280575
        rcases Nat.lt_or_ge n 173741007 with hs3 | hs3
        · -- n < 173741007
          rcases Nat.lt_or_ge n 173561151 with hs4 | hs4
          · -- n < 173561151
            rcases Nat.lt_or_ge n 173381294 with hs5 | hs5
            · -- n < 173381294
              exact Brocard.berndt_galway_chunk_0964 n m (by omega) (by omega) h
            · -- n >= 173381294
              exact Brocard.berndt_galway_chunk_0965 n m (by omega) (by omega) h
          · -- n >= 173561151
            exact Brocard.berndt_galway_chunk_0966 n m (by omega) (by omega) h
        · -- n >= 173741007
          rcases Nat.lt_or_ge n 174100719 with hs4 | hs4
          · -- n < 174100719
            rcases Nat.lt_or_ge n 173920863 with hs5 | hs5
            · -- n < 173920863
              exact Brocard.berndt_galway_chunk_0967 n m (by omega) (by omega) h
            · -- n >= 173920863
              exact Brocard.berndt_galway_chunk_0968 n m (by omega) (by omega) h
          · -- n >= 174100719
            exact Brocard.berndt_galway_chunk_0969 n m (by omega) (by omega) h
      · -- n >= 174280575
        rcases Nat.lt_or_ge n 174820143 with hs3 | hs3
        · -- n < 174820143
          rcases Nat.lt_or_ge n 174640287 with hs4 | hs4
          · -- n < 174640287
            rcases Nat.lt_or_ge n 174460431 with hs5 | hs5
            · -- n < 174460431
              exact Brocard.berndt_galway_chunk_0970 n m (by omega) (by omega) h
            · -- n >= 174460431
              exact Brocard.berndt_galway_chunk_0971 n m (by omega) (by omega) h
          · -- n >= 174640287
            exact Brocard.berndt_galway_chunk_0972 n m (by omega) (by omega) h
        · -- n >= 174820143
          rcases Nat.lt_or_ge n 175000000 with hs4 | hs4
          · -- n < 175000000
            exact Brocard.berndt_galway_chunk_0973 n m (by omega) (by omega) h
          · -- n >= 175000000
            exact Brocard.berndt_galway_chunk_0974 n m (by omega) (by omega) h
