-- Prove2me | solution 1 for Brocard.berndt_galway_group_045
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:44:34.668418+00:00
-- url     : https://prove2.me/submissions/6be53560-3b68-46cb-9eaa-42697e4eb49f

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_2041
import Theorems.Thm_Brocard_berndt_galway_chunk_2042
import Theorems.Thm_Brocard_berndt_galway_chunk_2043
import Theorems.Thm_Brocard_berndt_galway_chunk_2044
import Theorems.Thm_Brocard_berndt_galway_chunk_2045
import Theorems.Thm_Brocard_berndt_galway_chunk_2046
import Theorems.Thm_Brocard_berndt_galway_chunk_2047
import Theorems.Thm_Brocard_berndt_galway_chunk_2048
import Theorems.Thm_Brocard_berndt_galway_chunk_2049
import Theorems.Thm_Brocard_berndt_galway_chunk_2050
import Theorems.Thm_Brocard_berndt_galway_chunk_2051
import Theorems.Thm_Brocard_berndt_galway_chunk_2052
import Theorems.Thm_Brocard_berndt_galway_chunk_2053
import Theorems.Thm_Brocard_berndt_galway_chunk_2054
import Theorems.Thm_Brocard_berndt_galway_chunk_2055
import Theorems.Thm_Brocard_berndt_galway_chunk_2056
import Theorems.Thm_Brocard_berndt_galway_chunk_2057
import Theorems.Thm_Brocard_berndt_galway_chunk_2058
import Theorems.Thm_Brocard_berndt_galway_chunk_2059
import Theorems.Thm_Brocard_berndt_galway_chunk_2060
import Theorems.Thm_Brocard_berndt_galway_chunk_2061
import Theorems.Thm_Brocard_berndt_galway_chunk_2062
import Theorems.Thm_Brocard_berndt_galway_chunk_2063
import Theorems.Thm_Brocard_berndt_galway_chunk_2064
import Theorems.Thm_Brocard_berndt_galway_chunk_2065
import Theorems.Thm_Brocard_berndt_galway_chunk_2066
import Theorems.Thm_Brocard_berndt_galway_chunk_2067
import Theorems.Thm_Brocard_berndt_galway_chunk_2068
import Theorems.Thm_Brocard_berndt_galway_chunk_2069
import Theorems.Thm_Brocard_berndt_galway_chunk_2070
import Theorems.Thm_Brocard_berndt_galway_chunk_2071
import Theorems.Thm_Brocard_berndt_galway_chunk_2072
import Theorems.Thm_Brocard_berndt_galway_chunk_2073
import Theorems.Thm_Brocard_berndt_galway_chunk_2074
import Theorems.Thm_Brocard_berndt_galway_chunk_2075
import Theorems.Thm_Brocard_berndt_galway_chunk_2076
import Theorems.Thm_Brocard_berndt_galway_chunk_2077
import Theorems.Thm_Brocard_berndt_galway_chunk_2078
import Theorems.Thm_Brocard_berndt_galway_chunk_2079
import Theorems.Thm_Brocard_berndt_galway_chunk_2080
import Theorems.Thm_Brocard_berndt_galway_chunk_2081
import Theorems.Thm_Brocard_berndt_galway_chunk_2082
import Theorems.Thm_Brocard_berndt_galway_chunk_2083
import Theorems.Thm_Brocard_berndt_galway_chunk_2084
import Theorems.Thm_Brocard_berndt_galway_chunk_2085
import Theorems.Thm_Brocard_berndt_galway_chunk_2086

theorem solution (n m : ℕ) (h1 : 366906474 ≤ n) (h2 : n < 375179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 371043165 with hs0 | hs0
  · -- n < 371043165
    rcases Nat.lt_or_ge n 369064748 with hs1 | hs1
    · -- n < 369064748
      rcases Nat.lt_or_ge n 367985611 with hs2 | hs2
      · -- n < 367985611
        rcases Nat.lt_or_ge n 367446043 with hs3 | hs3
        · -- n < 367446043
          rcases Nat.lt_or_ge n 367266187 with hs4 | hs4
          · -- n < 367266187
            rcases Nat.lt_or_ge n 367086330 with hs5 | hs5
            · -- n < 367086330
              exact Brocard.berndt_galway_chunk_2041 n m (by omega) (by omega) h
            · -- n >= 367086330
              exact Brocard.berndt_galway_chunk_2042 n m (by omega) (by omega) h
          · -- n >= 367266187
            exact Brocard.berndt_galway_chunk_2043 n m (by omega) (by omega) h
        · -- n >= 367446043
          rcases Nat.lt_or_ge n 367805755 with hs4 | hs4
          · -- n < 367805755
            rcases Nat.lt_or_ge n 367625899 with hs5 | hs5
            · -- n < 367625899
              exact Brocard.berndt_galway_chunk_2044 n m (by omega) (by omega) h
            · -- n >= 367625899
              exact Brocard.berndt_galway_chunk_2045 n m (by omega) (by omega) h
          · -- n >= 367805755
            exact Brocard.berndt_galway_chunk_2046 n m (by omega) (by omega) h
      · -- n >= 367985611
        rcases Nat.lt_or_ge n 368525179 with hs3 | hs3
        · -- n < 368525179
          rcases Nat.lt_or_ge n 368345323 with hs4 | hs4
          · -- n < 368345323
            rcases Nat.lt_or_ge n 368165467 with hs5 | hs5
            · -- n < 368165467
              exact Brocard.berndt_galway_chunk_2047 n m (by omega) (by omega) h
            · -- n >= 368165467
              exact Brocard.berndt_galway_chunk_2048 n m (by omega) (by omega) h
          · -- n >= 368345323
            exact Brocard.berndt_galway_chunk_2049 n m (by omega) (by omega) h
        · -- n >= 368525179
          rcases Nat.lt_or_ge n 368884892 with hs4 | hs4
          · -- n < 368884892
            rcases Nat.lt_or_ge n 368705035 with hs5 | hs5
            · -- n < 368705035
              exact Brocard.berndt_galway_chunk_2050 n m (by omega) (by omega) h
            · -- n >= 368705035
              exact Brocard.berndt_galway_chunk_2051 n m (by omega) (by omega) h
          · -- n >= 368884892
            exact Brocard.berndt_galway_chunk_2052 n m (by omega) (by omega) h
    · -- n >= 369064748
      rcases Nat.lt_or_ge n 370143884 with hs2 | hs2
      · -- n < 370143884
        rcases Nat.lt_or_ge n 369604316 with hs3 | hs3
        · -- n < 369604316
          rcases Nat.lt_or_ge n 369424460 with hs4 | hs4
          · -- n < 369424460
            rcases Nat.lt_or_ge n 369244604 with hs5 | hs5
            · -- n < 369244604
              exact Brocard.berndt_galway_chunk_2053 n m (by omega) (by omega) h
            · -- n >= 369244604
              exact Brocard.berndt_galway_chunk_2054 n m (by omega) (by omega) h
          · -- n >= 369424460
            exact Brocard.berndt_galway_chunk_2055 n m (by omega) (by omega) h
        · -- n >= 369604316
          rcases Nat.lt_or_ge n 369964028 with hs4 | hs4
          · -- n < 369964028
            rcases Nat.lt_or_ge n 369784172 with hs5 | hs5
            · -- n < 369784172
              exact Brocard.berndt_galway_chunk_2056 n m (by omega) (by omega) h
            · -- n >= 369784172
              exact Brocard.berndt_galway_chunk_2057 n m (by omega) (by omega) h
          · -- n >= 369964028
            exact Brocard.berndt_galway_chunk_2058 n m (by omega) (by omega) h
      · -- n >= 370143884
        rcases Nat.lt_or_ge n 370683453 with hs3 | hs3
        · -- n < 370683453
          rcases Nat.lt_or_ge n 370503597 with hs4 | hs4
          · -- n < 370503597
            rcases Nat.lt_or_ge n 370323741 with hs5 | hs5
            · -- n < 370323741
              exact Brocard.berndt_galway_chunk_2059 n m (by omega) (by omega) h
            · -- n >= 370323741
              exact Brocard.berndt_galway_chunk_2060 n m (by omega) (by omega) h
          · -- n >= 370503597
            exact Brocard.berndt_galway_chunk_2061 n m (by omega) (by omega) h
        · -- n >= 370683453
          rcases Nat.lt_or_ge n 370863309 with hs4 | hs4
          · -- n < 370863309
            exact Brocard.berndt_galway_chunk_2062 n m (by omega) (by omega) h
          · -- n >= 370863309
            exact Brocard.berndt_galway_chunk_2063 n m (by omega) (by omega) h
  · -- n >= 371043165
    rcases Nat.lt_or_ge n 373201438 with hs1 | hs1
    · -- n < 373201438
      rcases Nat.lt_or_ge n 372122302 with hs2 | hs2
      · -- n < 372122302
        rcases Nat.lt_or_ge n 371582733 with hs3 | hs3
        · -- n < 371582733
          rcases Nat.lt_or_ge n 371402877 with hs4 | hs4
          · -- n < 371402877
            rcases Nat.lt_or_ge n 371223021 with hs5 | hs5
            · -- n < 371223021
              exact Brocard.berndt_galway_chunk_2064 n m (by omega) (by omega) h
            · -- n >= 371223021
              exact Brocard.berndt_galway_chunk_2065 n m (by omega) (by omega) h
          · -- n >= 371402877
            exact Brocard.berndt_galway_chunk_2066 n m (by omega) (by omega) h
        · -- n >= 371582733
          rcases Nat.lt_or_ge n 371942446 with hs4 | hs4
          · -- n < 371942446
            rcases Nat.lt_or_ge n 371762589 with hs5 | hs5
            · -- n < 371762589
              exact Brocard.berndt_galway_chunk_2067 n m (by omega) (by omega) h
            · -- n >= 371762589
              exact Brocard.berndt_galway_chunk_2068 n m (by omega) (by omega) h
          · -- n >= 371942446
            exact Brocard.berndt_galway_chunk_2069 n m (by omega) (by omega) h
      · -- n >= 372122302
        rcases Nat.lt_or_ge n 372661870 with hs3 | hs3
        · -- n < 372661870
          rcases Nat.lt_or_ge n 372482014 with hs4 | hs4
          · -- n < 372482014
            rcases Nat.lt_or_ge n 372302158 with hs5 | hs5
            · -- n < 372302158
              exact Brocard.berndt_galway_chunk_2070 n m (by omega) (by omega) h
            · -- n >= 372302158
              exact Brocard.berndt_galway_chunk_2071 n m (by omega) (by omega) h
          · -- n >= 372482014
            exact Brocard.berndt_galway_chunk_2072 n m (by omega) (by omega) h
        · -- n >= 372661870
          rcases Nat.lt_or_ge n 373021582 with hs4 | hs4
          · -- n < 373021582
            rcases Nat.lt_or_ge n 372841726 with hs5 | hs5
            · -- n < 372841726
              exact Brocard.berndt_galway_chunk_2073 n m (by omega) (by omega) h
            · -- n >= 372841726
              exact Brocard.berndt_galway_chunk_2074 n m (by omega) (by omega) h
          · -- n >= 373021582
            exact Brocard.berndt_galway_chunk_2075 n m (by omega) (by omega) h
    · -- n >= 373201438
      rcases Nat.lt_or_ge n 374280575 with hs2 | hs2
      · -- n < 374280575
        rcases Nat.lt_or_ge n 373741007 with hs3 | hs3
        · -- n < 373741007
          rcases Nat.lt_or_ge n 373561151 with hs4 | hs4
          · -- n < 373561151
            rcases Nat.lt_or_ge n 373381294 with hs5 | hs5
            · -- n < 373381294
              exact Brocard.berndt_galway_chunk_2076 n m (by omega) (by omega) h
            · -- n >= 373381294
              exact Brocard.berndt_galway_chunk_2077 n m (by omega) (by omega) h
          · -- n >= 373561151
            exact Brocard.berndt_galway_chunk_2078 n m (by omega) (by omega) h
        · -- n >= 373741007
          rcases Nat.lt_or_ge n 374100719 with hs4 | hs4
          · -- n < 374100719
            rcases Nat.lt_or_ge n 373920863 with hs5 | hs5
            · -- n < 373920863
              exact Brocard.berndt_galway_chunk_2079 n m (by omega) (by omega) h
            · -- n >= 373920863
              exact Brocard.berndt_galway_chunk_2080 n m (by omega) (by omega) h
          · -- n >= 374100719
            exact Brocard.berndt_galway_chunk_2081 n m (by omega) (by omega) h
      · -- n >= 374280575
        rcases Nat.lt_or_ge n 374820143 with hs3 | hs3
        · -- n < 374820143
          rcases Nat.lt_or_ge n 374640287 with hs4 | hs4
          · -- n < 374640287
            rcases Nat.lt_or_ge n 374460431 with hs5 | hs5
            · -- n < 374460431
              exact Brocard.berndt_galway_chunk_2082 n m (by omega) (by omega) h
            · -- n >= 374460431
              exact Brocard.berndt_galway_chunk_2083 n m (by omega) (by omega) h
          · -- n >= 374640287
            exact Brocard.berndt_galway_chunk_2084 n m (by omega) (by omega) h
        · -- n >= 374820143
          rcases Nat.lt_or_ge n 375000000 with hs4 | hs4
          · -- n < 375000000
            exact Brocard.berndt_galway_chunk_2085 n m (by omega) (by omega) h
          · -- n >= 375000000
            exact Brocard.berndt_galway_chunk_2086 n m (by omega) (by omega) h
