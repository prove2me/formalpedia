-- Prove2me | solution 1 for Brocard.berndt_galway_group_108
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:36:40.001293+00:00
-- url     : https://prove2.me/submissions/de62af31-174d-435b-a80e-42121ecb8b21

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_4959
import Theorems.Thm_Brocard_berndt_galway_chunk_4960
import Theorems.Thm_Brocard_berndt_galway_chunk_4961
import Theorems.Thm_Brocard_berndt_galway_chunk_4962
import Theorems.Thm_Brocard_berndt_galway_chunk_4963
import Theorems.Thm_Brocard_berndt_galway_chunk_4964
import Theorems.Thm_Brocard_berndt_galway_chunk_4965
import Theorems.Thm_Brocard_berndt_galway_chunk_4966
import Theorems.Thm_Brocard_berndt_galway_chunk_4967
import Theorems.Thm_Brocard_berndt_galway_chunk_4968
import Theorems.Thm_Brocard_berndt_galway_chunk_4969
import Theorems.Thm_Brocard_berndt_galway_chunk_4970
import Theorems.Thm_Brocard_berndt_galway_chunk_4971
import Theorems.Thm_Brocard_berndt_galway_chunk_4972
import Theorems.Thm_Brocard_berndt_galway_chunk_4973
import Theorems.Thm_Brocard_berndt_galway_chunk_4974
import Theorems.Thm_Brocard_berndt_galway_chunk_4975
import Theorems.Thm_Brocard_berndt_galway_chunk_4976
import Theorems.Thm_Brocard_berndt_galway_chunk_4977
import Theorems.Thm_Brocard_berndt_galway_chunk_4978
import Theorems.Thm_Brocard_berndt_galway_chunk_4979
import Theorems.Thm_Brocard_berndt_galway_chunk_4980
import Theorems.Thm_Brocard_berndt_galway_chunk_4981
import Theorems.Thm_Brocard_berndt_galway_chunk_4982
import Theorems.Thm_Brocard_berndt_galway_chunk_4983
import Theorems.Thm_Brocard_berndt_galway_chunk_4984
import Theorems.Thm_Brocard_berndt_galway_chunk_4985
import Theorems.Thm_Brocard_berndt_galway_chunk_4986
import Theorems.Thm_Brocard_berndt_galway_chunk_4987
import Theorems.Thm_Brocard_berndt_galway_chunk_4988
import Theorems.Thm_Brocard_berndt_galway_chunk_4989
import Theorems.Thm_Brocard_berndt_galway_chunk_4990
import Theorems.Thm_Brocard_berndt_galway_chunk_4991
import Theorems.Thm_Brocard_berndt_galway_chunk_4992
import Theorems.Thm_Brocard_berndt_galway_chunk_4993
import Theorems.Thm_Brocard_berndt_galway_chunk_4994
import Theorems.Thm_Brocard_berndt_galway_chunk_4995
import Theorems.Thm_Brocard_berndt_galway_chunk_4996
import Theorems.Thm_Brocard_berndt_galway_chunk_4997
import Theorems.Thm_Brocard_berndt_galway_chunk_4998
import Theorems.Thm_Brocard_berndt_galway_chunk_4999
import Theorems.Thm_Brocard_berndt_galway_chunk_5000
import Theorems.Thm_Brocard_berndt_galway_chunk_5001
import Theorems.Thm_Brocard_berndt_galway_chunk_5002
import Theorems.Thm_Brocard_berndt_galway_chunk_5003
import Theorems.Thm_Brocard_berndt_galway_chunk_5004

theorem solution (n m : ℕ) (h1 : 891726618 ≤ n) (h2 : n < 900000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 895863309 with hs0 | hs0
  · -- n < 895863309
    rcases Nat.lt_or_ge n 893884892 with hs1 | hs1
    · -- n < 893884892
      rcases Nat.lt_or_ge n 892805755 with hs2 | hs2
      · -- n < 892805755
        rcases Nat.lt_or_ge n 892266187 with hs3 | hs3
        · -- n < 892266187
          rcases Nat.lt_or_ge n 892086330 with hs4 | hs4
          · -- n < 892086330
            rcases Nat.lt_or_ge n 891906474 with hs5 | hs5
            · -- n < 891906474
              exact Brocard.berndt_galway_chunk_4959 n m (by omega) (by omega) h
            · -- n >= 891906474
              exact Brocard.berndt_galway_chunk_4960 n m (by omega) (by omega) h
          · -- n >= 892086330
            exact Brocard.berndt_galway_chunk_4961 n m (by omega) (by omega) h
        · -- n >= 892266187
          rcases Nat.lt_or_ge n 892625899 with hs4 | hs4
          · -- n < 892625899
            rcases Nat.lt_or_ge n 892446043 with hs5 | hs5
            · -- n < 892446043
              exact Brocard.berndt_galway_chunk_4962 n m (by omega) (by omega) h
            · -- n >= 892446043
              exact Brocard.berndt_galway_chunk_4963 n m (by omega) (by omega) h
          · -- n >= 892625899
            exact Brocard.berndt_galway_chunk_4964 n m (by omega) (by omega) h
      · -- n >= 892805755
        rcases Nat.lt_or_ge n 893345323 with hs3 | hs3
        · -- n < 893345323
          rcases Nat.lt_or_ge n 893165467 with hs4 | hs4
          · -- n < 893165467
            rcases Nat.lt_or_ge n 892985611 with hs5 | hs5
            · -- n < 892985611
              exact Brocard.berndt_galway_chunk_4965 n m (by omega) (by omega) h
            · -- n >= 892985611
              exact Brocard.berndt_galway_chunk_4966 n m (by omega) (by omega) h
          · -- n >= 893165467
            exact Brocard.berndt_galway_chunk_4967 n m (by omega) (by omega) h
        · -- n >= 893345323
          rcases Nat.lt_or_ge n 893705035 with hs4 | hs4
          · -- n < 893705035
            rcases Nat.lt_or_ge n 893525179 with hs5 | hs5
            · -- n < 893525179
              exact Brocard.berndt_galway_chunk_4968 n m (by omega) (by omega) h
            · -- n >= 893525179
              exact Brocard.berndt_galway_chunk_4969 n m (by omega) (by omega) h
          · -- n >= 893705035
            exact Brocard.berndt_galway_chunk_4970 n m (by omega) (by omega) h
    · -- n >= 893884892
      rcases Nat.lt_or_ge n 894964028 with hs2 | hs2
      · -- n < 894964028
        rcases Nat.lt_or_ge n 894424460 with hs3 | hs3
        · -- n < 894424460
          rcases Nat.lt_or_ge n 894244604 with hs4 | hs4
          · -- n < 894244604
            rcases Nat.lt_or_ge n 894064748 with hs5 | hs5
            · -- n < 894064748
              exact Brocard.berndt_galway_chunk_4971 n m (by omega) (by omega) h
            · -- n >= 894064748
              exact Brocard.berndt_galway_chunk_4972 n m (by omega) (by omega) h
          · -- n >= 894244604
            exact Brocard.berndt_galway_chunk_4973 n m (by omega) (by omega) h
        · -- n >= 894424460
          rcases Nat.lt_or_ge n 894784172 with hs4 | hs4
          · -- n < 894784172
            rcases Nat.lt_or_ge n 894604316 with hs5 | hs5
            · -- n < 894604316
              exact Brocard.berndt_galway_chunk_4974 n m (by omega) (by omega) h
            · -- n >= 894604316
              exact Brocard.berndt_galway_chunk_4975 n m (by omega) (by omega) h
          · -- n >= 894784172
            exact Brocard.berndt_galway_chunk_4976 n m (by omega) (by omega) h
      · -- n >= 894964028
        rcases Nat.lt_or_ge n 895503597 with hs3 | hs3
        · -- n < 895503597
          rcases Nat.lt_or_ge n 895323741 with hs4 | hs4
          · -- n < 895323741
            rcases Nat.lt_or_ge n 895143884 with hs5 | hs5
            · -- n < 895143884
              exact Brocard.berndt_galway_chunk_4977 n m (by omega) (by omega) h
            · -- n >= 895143884
              exact Brocard.berndt_galway_chunk_4978 n m (by omega) (by omega) h
          · -- n >= 895323741
            exact Brocard.berndt_galway_chunk_4979 n m (by omega) (by omega) h
        · -- n >= 895503597
          rcases Nat.lt_or_ge n 895683453 with hs4 | hs4
          · -- n < 895683453
            exact Brocard.berndt_galway_chunk_4980 n m (by omega) (by omega) h
          · -- n >= 895683453
            exact Brocard.berndt_galway_chunk_4981 n m (by omega) (by omega) h
  · -- n >= 895863309
    rcases Nat.lt_or_ge n 898021582 with hs1 | hs1
    · -- n < 898021582
      rcases Nat.lt_or_ge n 896942446 with hs2 | hs2
      · -- n < 896942446
        rcases Nat.lt_or_ge n 896402877 with hs3 | hs3
        · -- n < 896402877
          rcases Nat.lt_or_ge n 896223021 with hs4 | hs4
          · -- n < 896223021
            rcases Nat.lt_or_ge n 896043165 with hs5 | hs5
            · -- n < 896043165
              exact Brocard.berndt_galway_chunk_4982 n m (by omega) (by omega) h
            · -- n >= 896043165
              exact Brocard.berndt_galway_chunk_4983 n m (by omega) (by omega) h
          · -- n >= 896223021
            exact Brocard.berndt_galway_chunk_4984 n m (by omega) (by omega) h
        · -- n >= 896402877
          rcases Nat.lt_or_ge n 896762589 with hs4 | hs4
          · -- n < 896762589
            rcases Nat.lt_or_ge n 896582733 with hs5 | hs5
            · -- n < 896582733
              exact Brocard.berndt_galway_chunk_4985 n m (by omega) (by omega) h
            · -- n >= 896582733
              exact Brocard.berndt_galway_chunk_4986 n m (by omega) (by omega) h
          · -- n >= 896762589
            exact Brocard.berndt_galway_chunk_4987 n m (by omega) (by omega) h
      · -- n >= 896942446
        rcases Nat.lt_or_ge n 897482014 with hs3 | hs3
        · -- n < 897482014
          rcases Nat.lt_or_ge n 897302158 with hs4 | hs4
          · -- n < 897302158
            rcases Nat.lt_or_ge n 897122302 with hs5 | hs5
            · -- n < 897122302
              exact Brocard.berndt_galway_chunk_4988 n m (by omega) (by omega) h
            · -- n >= 897122302
              exact Brocard.berndt_galway_chunk_4989 n m (by omega) (by omega) h
          · -- n >= 897302158
            exact Brocard.berndt_galway_chunk_4990 n m (by omega) (by omega) h
        · -- n >= 897482014
          rcases Nat.lt_or_ge n 897841726 with hs4 | hs4
          · -- n < 897841726
            rcases Nat.lt_or_ge n 897661870 with hs5 | hs5
            · -- n < 897661870
              exact Brocard.berndt_galway_chunk_4991 n m (by omega) (by omega) h
            · -- n >= 897661870
              exact Brocard.berndt_galway_chunk_4992 n m (by omega) (by omega) h
          · -- n >= 897841726
            exact Brocard.berndt_galway_chunk_4993 n m (by omega) (by omega) h
    · -- n >= 898021582
      rcases Nat.lt_or_ge n 899100719 with hs2 | hs2
      · -- n < 899100719
        rcases Nat.lt_or_ge n 898561151 with hs3 | hs3
        · -- n < 898561151
          rcases Nat.lt_or_ge n 898381294 with hs4 | hs4
          · -- n < 898381294
            rcases Nat.lt_or_ge n 898201438 with hs5 | hs5
            · -- n < 898201438
              exact Brocard.berndt_galway_chunk_4994 n m (by omega) (by omega) h
            · -- n >= 898201438
              exact Brocard.berndt_galway_chunk_4995 n m (by omega) (by omega) h
          · -- n >= 898381294
            exact Brocard.berndt_galway_chunk_4996 n m (by omega) (by omega) h
        · -- n >= 898561151
          rcases Nat.lt_or_ge n 898920863 with hs4 | hs4
          · -- n < 898920863
            rcases Nat.lt_or_ge n 898741007 with hs5 | hs5
            · -- n < 898741007
              exact Brocard.berndt_galway_chunk_4997 n m (by omega) (by omega) h
            · -- n >= 898741007
              exact Brocard.berndt_galway_chunk_4998 n m (by omega) (by omega) h
          · -- n >= 898920863
            exact Brocard.berndt_galway_chunk_4999 n m (by omega) (by omega) h
      · -- n >= 899100719
        rcases Nat.lt_or_ge n 899640287 with hs3 | hs3
        · -- n < 899640287
          rcases Nat.lt_or_ge n 899460431 with hs4 | hs4
          · -- n < 899460431
            rcases Nat.lt_or_ge n 899280575 with hs5 | hs5
            · -- n < 899280575
              exact Brocard.berndt_galway_chunk_5000 n m (by omega) (by omega) h
            · -- n >= 899280575
              exact Brocard.berndt_galway_chunk_5001 n m (by omega) (by omega) h
          · -- n >= 899460431
            exact Brocard.berndt_galway_chunk_5002 n m (by omega) (by omega) h
        · -- n >= 899640287
          rcases Nat.lt_or_ge n 899820143 with hs4 | hs4
          · -- n < 899820143
            exact Brocard.berndt_galway_chunk_5003 n m (by omega) (by omega) h
          · -- n >= 899820143
            exact Brocard.berndt_galway_chunk_5004 n m (by omega) (by omega) h
