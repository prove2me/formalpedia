-- Prove2me | solution 1 for Brocard.berndt_galway_group_024
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:26:34.86424+00:00
-- url     : https://prove2.me/submissions/99adebff-5cad-4b06-880d-6735c6e66900

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_1067
import Theorems.Thm_Brocard_berndt_galway_chunk_1068
import Theorems.Thm_Brocard_berndt_galway_chunk_1069
import Theorems.Thm_Brocard_berndt_galway_chunk_1070
import Theorems.Thm_Brocard_berndt_galway_chunk_1071
import Theorems.Thm_Brocard_berndt_galway_chunk_1072
import Theorems.Thm_Brocard_berndt_galway_chunk_1073
import Theorems.Thm_Brocard_berndt_galway_chunk_1074
import Theorems.Thm_Brocard_berndt_galway_chunk_1075
import Theorems.Thm_Brocard_berndt_galway_chunk_1076
import Theorems.Thm_Brocard_berndt_galway_chunk_1077
import Theorems.Thm_Brocard_berndt_galway_chunk_1078
import Theorems.Thm_Brocard_berndt_galway_chunk_1079
import Theorems.Thm_Brocard_berndt_galway_chunk_1080
import Theorems.Thm_Brocard_berndt_galway_chunk_1081
import Theorems.Thm_Brocard_berndt_galway_chunk_1082
import Theorems.Thm_Brocard_berndt_galway_chunk_1083
import Theorems.Thm_Brocard_berndt_galway_chunk_1084
import Theorems.Thm_Brocard_berndt_galway_chunk_1085
import Theorems.Thm_Brocard_berndt_galway_chunk_1086
import Theorems.Thm_Brocard_berndt_galway_chunk_1087
import Theorems.Thm_Brocard_berndt_galway_chunk_1088
import Theorems.Thm_Brocard_berndt_galway_chunk_1089
import Theorems.Thm_Brocard_berndt_galway_chunk_1090
import Theorems.Thm_Brocard_berndt_galway_chunk_1091
import Theorems.Thm_Brocard_berndt_galway_chunk_1092
import Theorems.Thm_Brocard_berndt_galway_chunk_1093
import Theorems.Thm_Brocard_berndt_galway_chunk_1094
import Theorems.Thm_Brocard_berndt_galway_chunk_1095
import Theorems.Thm_Brocard_berndt_galway_chunk_1096
import Theorems.Thm_Brocard_berndt_galway_chunk_1097
import Theorems.Thm_Brocard_berndt_galway_chunk_1098
import Theorems.Thm_Brocard_berndt_galway_chunk_1099
import Theorems.Thm_Brocard_berndt_galway_chunk_1100
import Theorems.Thm_Brocard_berndt_galway_chunk_1101
import Theorems.Thm_Brocard_berndt_galway_chunk_1102
import Theorems.Thm_Brocard_berndt_galway_chunk_1103
import Theorems.Thm_Brocard_berndt_galway_chunk_1104
import Theorems.Thm_Brocard_berndt_galway_chunk_1105
import Theorems.Thm_Brocard_berndt_galway_chunk_1106
import Theorems.Thm_Brocard_berndt_galway_chunk_1107
import Theorems.Thm_Brocard_berndt_galway_chunk_1108
import Theorems.Thm_Brocard_berndt_galway_chunk_1109
import Theorems.Thm_Brocard_berndt_galway_chunk_1110
import Theorems.Thm_Brocard_berndt_galway_chunk_1111
import Theorems.Thm_Brocard_berndt_galway_chunk_1112

theorem solution (n m : ℕ) (h1 : 191726618 ≤ n) (h2 : n < 200000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 195863309 with hs0 | hs0
  · -- n < 195863309
    rcases Nat.lt_or_ge n 193884892 with hs1 | hs1
    · -- n < 193884892
      rcases Nat.lt_or_ge n 192805755 with hs2 | hs2
      · -- n < 192805755
        rcases Nat.lt_or_ge n 192266187 with hs3 | hs3
        · -- n < 192266187
          rcases Nat.lt_or_ge n 192086330 with hs4 | hs4
          · -- n < 192086330
            rcases Nat.lt_or_ge n 191906474 with hs5 | hs5
            · -- n < 191906474
              exact Brocard.berndt_galway_chunk_1067 n m (by omega) (by omega) h
            · -- n >= 191906474
              exact Brocard.berndt_galway_chunk_1068 n m (by omega) (by omega) h
          · -- n >= 192086330
            exact Brocard.berndt_galway_chunk_1069 n m (by omega) (by omega) h
        · -- n >= 192266187
          rcases Nat.lt_or_ge n 192625899 with hs4 | hs4
          · -- n < 192625899
            rcases Nat.lt_or_ge n 192446043 with hs5 | hs5
            · -- n < 192446043
              exact Brocard.berndt_galway_chunk_1070 n m (by omega) (by omega) h
            · -- n >= 192446043
              exact Brocard.berndt_galway_chunk_1071 n m (by omega) (by omega) h
          · -- n >= 192625899
            exact Brocard.berndt_galway_chunk_1072 n m (by omega) (by omega) h
      · -- n >= 192805755
        rcases Nat.lt_or_ge n 193345323 with hs3 | hs3
        · -- n < 193345323
          rcases Nat.lt_or_ge n 193165467 with hs4 | hs4
          · -- n < 193165467
            rcases Nat.lt_or_ge n 192985611 with hs5 | hs5
            · -- n < 192985611
              exact Brocard.berndt_galway_chunk_1073 n m (by omega) (by omega) h
            · -- n >= 192985611
              exact Brocard.berndt_galway_chunk_1074 n m (by omega) (by omega) h
          · -- n >= 193165467
            exact Brocard.berndt_galway_chunk_1075 n m (by omega) (by omega) h
        · -- n >= 193345323
          rcases Nat.lt_or_ge n 193705035 with hs4 | hs4
          · -- n < 193705035
            rcases Nat.lt_or_ge n 193525179 with hs5 | hs5
            · -- n < 193525179
              exact Brocard.berndt_galway_chunk_1076 n m (by omega) (by omega) h
            · -- n >= 193525179
              exact Brocard.berndt_galway_chunk_1077 n m (by omega) (by omega) h
          · -- n >= 193705035
            exact Brocard.berndt_galway_chunk_1078 n m (by omega) (by omega) h
    · -- n >= 193884892
      rcases Nat.lt_or_ge n 194964028 with hs2 | hs2
      · -- n < 194964028
        rcases Nat.lt_or_ge n 194424460 with hs3 | hs3
        · -- n < 194424460
          rcases Nat.lt_or_ge n 194244604 with hs4 | hs4
          · -- n < 194244604
            rcases Nat.lt_or_ge n 194064748 with hs5 | hs5
            · -- n < 194064748
              exact Brocard.berndt_galway_chunk_1079 n m (by omega) (by omega) h
            · -- n >= 194064748
              exact Brocard.berndt_galway_chunk_1080 n m (by omega) (by omega) h
          · -- n >= 194244604
            exact Brocard.berndt_galway_chunk_1081 n m (by omega) (by omega) h
        · -- n >= 194424460
          rcases Nat.lt_or_ge n 194784172 with hs4 | hs4
          · -- n < 194784172
            rcases Nat.lt_or_ge n 194604316 with hs5 | hs5
            · -- n < 194604316
              exact Brocard.berndt_galway_chunk_1082 n m (by omega) (by omega) h
            · -- n >= 194604316
              exact Brocard.berndt_galway_chunk_1083 n m (by omega) (by omega) h
          · -- n >= 194784172
            exact Brocard.berndt_galway_chunk_1084 n m (by omega) (by omega) h
      · -- n >= 194964028
        rcases Nat.lt_or_ge n 195503597 with hs3 | hs3
        · -- n < 195503597
          rcases Nat.lt_or_ge n 195323741 with hs4 | hs4
          · -- n < 195323741
            rcases Nat.lt_or_ge n 195143884 with hs5 | hs5
            · -- n < 195143884
              exact Brocard.berndt_galway_chunk_1085 n m (by omega) (by omega) h
            · -- n >= 195143884
              exact Brocard.berndt_galway_chunk_1086 n m (by omega) (by omega) h
          · -- n >= 195323741
            exact Brocard.berndt_galway_chunk_1087 n m (by omega) (by omega) h
        · -- n >= 195503597
          rcases Nat.lt_or_ge n 195683453 with hs4 | hs4
          · -- n < 195683453
            exact Brocard.berndt_galway_chunk_1088 n m (by omega) (by omega) h
          · -- n >= 195683453
            exact Brocard.berndt_galway_chunk_1089 n m (by omega) (by omega) h
  · -- n >= 195863309
    rcases Nat.lt_or_ge n 198021582 with hs1 | hs1
    · -- n < 198021582
      rcases Nat.lt_or_ge n 196942446 with hs2 | hs2
      · -- n < 196942446
        rcases Nat.lt_or_ge n 196402877 with hs3 | hs3
        · -- n < 196402877
          rcases Nat.lt_or_ge n 196223021 with hs4 | hs4
          · -- n < 196223021
            rcases Nat.lt_or_ge n 196043165 with hs5 | hs5
            · -- n < 196043165
              exact Brocard.berndt_galway_chunk_1090 n m (by omega) (by omega) h
            · -- n >= 196043165
              exact Brocard.berndt_galway_chunk_1091 n m (by omega) (by omega) h
          · -- n >= 196223021
            exact Brocard.berndt_galway_chunk_1092 n m (by omega) (by omega) h
        · -- n >= 196402877
          rcases Nat.lt_or_ge n 196762589 with hs4 | hs4
          · -- n < 196762589
            rcases Nat.lt_or_ge n 196582733 with hs5 | hs5
            · -- n < 196582733
              exact Brocard.berndt_galway_chunk_1093 n m (by omega) (by omega) h
            · -- n >= 196582733
              exact Brocard.berndt_galway_chunk_1094 n m (by omega) (by omega) h
          · -- n >= 196762589
            exact Brocard.berndt_galway_chunk_1095 n m (by omega) (by omega) h
      · -- n >= 196942446
        rcases Nat.lt_or_ge n 197482014 with hs3 | hs3
        · -- n < 197482014
          rcases Nat.lt_or_ge n 197302158 with hs4 | hs4
          · -- n < 197302158
            rcases Nat.lt_or_ge n 197122302 with hs5 | hs5
            · -- n < 197122302
              exact Brocard.berndt_galway_chunk_1096 n m (by omega) (by omega) h
            · -- n >= 197122302
              exact Brocard.berndt_galway_chunk_1097 n m (by omega) (by omega) h
          · -- n >= 197302158
            exact Brocard.berndt_galway_chunk_1098 n m (by omega) (by omega) h
        · -- n >= 197482014
          rcases Nat.lt_or_ge n 197841726 with hs4 | hs4
          · -- n < 197841726
            rcases Nat.lt_or_ge n 197661870 with hs5 | hs5
            · -- n < 197661870
              exact Brocard.berndt_galway_chunk_1099 n m (by omega) (by omega) h
            · -- n >= 197661870
              exact Brocard.berndt_galway_chunk_1100 n m (by omega) (by omega) h
          · -- n >= 197841726
            exact Brocard.berndt_galway_chunk_1101 n m (by omega) (by omega) h
    · -- n >= 198021582
      rcases Nat.lt_or_ge n 199100719 with hs2 | hs2
      · -- n < 199100719
        rcases Nat.lt_or_ge n 198561151 with hs3 | hs3
        · -- n < 198561151
          rcases Nat.lt_or_ge n 198381294 with hs4 | hs4
          · -- n < 198381294
            rcases Nat.lt_or_ge n 198201438 with hs5 | hs5
            · -- n < 198201438
              exact Brocard.berndt_galway_chunk_1102 n m (by omega) (by omega) h
            · -- n >= 198201438
              exact Brocard.berndt_galway_chunk_1103 n m (by omega) (by omega) h
          · -- n >= 198381294
            exact Brocard.berndt_galway_chunk_1104 n m (by omega) (by omega) h
        · -- n >= 198561151
          rcases Nat.lt_or_ge n 198920863 with hs4 | hs4
          · -- n < 198920863
            rcases Nat.lt_or_ge n 198741007 with hs5 | hs5
            · -- n < 198741007
              exact Brocard.berndt_galway_chunk_1105 n m (by omega) (by omega) h
            · -- n >= 198741007
              exact Brocard.berndt_galway_chunk_1106 n m (by omega) (by omega) h
          · -- n >= 198920863
            exact Brocard.berndt_galway_chunk_1107 n m (by omega) (by omega) h
      · -- n >= 199100719
        rcases Nat.lt_or_ge n 199640287 with hs3 | hs3
        · -- n < 199640287
          rcases Nat.lt_or_ge n 199460431 with hs4 | hs4
          · -- n < 199460431
            rcases Nat.lt_or_ge n 199280575 with hs5 | hs5
            · -- n < 199280575
              exact Brocard.berndt_galway_chunk_1108 n m (by omega) (by omega) h
            · -- n >= 199280575
              exact Brocard.berndt_galway_chunk_1109 n m (by omega) (by omega) h
          · -- n >= 199460431
            exact Brocard.berndt_galway_chunk_1110 n m (by omega) (by omega) h
        · -- n >= 199640287
          rcases Nat.lt_or_ge n 199820143 with hs4 | hs4
          · -- n < 199820143
            exact Brocard.berndt_galway_chunk_1111 n m (by omega) (by omega) h
          · -- n >= 199820143
            exact Brocard.berndt_galway_chunk_1112 n m (by omega) (by omega) h
