-- Prove2me | solution 1 for Brocard.berndt_galway_group_110
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:54:35.525863+00:00
-- url     : https://prove2.me/submissions/2fde2b23-9e6f-46ab-b794-0659636477ac

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_5052
import Theorems.Thm_Brocard_berndt_galway_chunk_5053
import Theorems.Thm_Brocard_berndt_galway_chunk_5054
import Theorems.Thm_Brocard_berndt_galway_chunk_5055
import Theorems.Thm_Brocard_berndt_galway_chunk_5056
import Theorems.Thm_Brocard_berndt_galway_chunk_5057
import Theorems.Thm_Brocard_berndt_galway_chunk_5058
import Theorems.Thm_Brocard_berndt_galway_chunk_5059
import Theorems.Thm_Brocard_berndt_galway_chunk_5060
import Theorems.Thm_Brocard_berndt_galway_chunk_5061
import Theorems.Thm_Brocard_berndt_galway_chunk_5062
import Theorems.Thm_Brocard_berndt_galway_chunk_5063
import Theorems.Thm_Brocard_berndt_galway_chunk_5064
import Theorems.Thm_Brocard_berndt_galway_chunk_5065
import Theorems.Thm_Brocard_berndt_galway_chunk_5066
import Theorems.Thm_Brocard_berndt_galway_chunk_5067
import Theorems.Thm_Brocard_berndt_galway_chunk_5068
import Theorems.Thm_Brocard_berndt_galway_chunk_5069
import Theorems.Thm_Brocard_berndt_galway_chunk_5070
import Theorems.Thm_Brocard_berndt_galway_chunk_5071
import Theorems.Thm_Brocard_berndt_galway_chunk_5072
import Theorems.Thm_Brocard_berndt_galway_chunk_5073
import Theorems.Thm_Brocard_berndt_galway_chunk_5074
import Theorems.Thm_Brocard_berndt_galway_chunk_5075
import Theorems.Thm_Brocard_berndt_galway_chunk_5076
import Theorems.Thm_Brocard_berndt_galway_chunk_5077
import Theorems.Thm_Brocard_berndt_galway_chunk_5078
import Theorems.Thm_Brocard_berndt_galway_chunk_5079
import Theorems.Thm_Brocard_berndt_galway_chunk_5080
import Theorems.Thm_Brocard_berndt_galway_chunk_5081
import Theorems.Thm_Brocard_berndt_galway_chunk_5082
import Theorems.Thm_Brocard_berndt_galway_chunk_5083
import Theorems.Thm_Brocard_berndt_galway_chunk_5084
import Theorems.Thm_Brocard_berndt_galway_chunk_5085
import Theorems.Thm_Brocard_berndt_galway_chunk_5086
import Theorems.Thm_Brocard_berndt_galway_chunk_5087
import Theorems.Thm_Brocard_berndt_galway_chunk_5088
import Theorems.Thm_Brocard_berndt_galway_chunk_5089
import Theorems.Thm_Brocard_berndt_galway_chunk_5090
import Theorems.Thm_Brocard_berndt_galway_chunk_5091
import Theorems.Thm_Brocard_berndt_galway_chunk_5092
import Theorems.Thm_Brocard_berndt_galway_chunk_5093
import Theorems.Thm_Brocard_berndt_galway_chunk_5094
import Theorems.Thm_Brocard_berndt_galway_chunk_5095
import Theorems.Thm_Brocard_berndt_galway_chunk_5096
import Theorems.Thm_Brocard_berndt_galway_chunk_5097
import Theorems.Thm_Brocard_berndt_galway_chunk_5098

theorem solution (n m : ℕ) (h1 : 908453237 ≤ n) (h2 : n < 916906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 912769784 with hs0 | hs0
  · -- n < 912769784
    rcases Nat.lt_or_ge n 910611510 with hs1 | hs1
    · -- n < 910611510
      rcases Nat.lt_or_ge n 909532374 with hs2 | hs2
      · -- n < 909532374
        rcases Nat.lt_or_ge n 908992805 with hs3 | hs3
        · -- n < 908992805
          rcases Nat.lt_or_ge n 908812949 with hs4 | hs4
          · -- n < 908812949
            rcases Nat.lt_or_ge n 908633093 with hs5 | hs5
            · -- n < 908633093
              exact Brocard.berndt_galway_chunk_5052 n m (by omega) (by omega) h
            · -- n >= 908633093
              exact Brocard.berndt_galway_chunk_5053 n m (by omega) (by omega) h
          · -- n >= 908812949
            exact Brocard.berndt_galway_chunk_5054 n m (by omega) (by omega) h
        · -- n >= 908992805
          rcases Nat.lt_or_ge n 909352517 with hs4 | hs4
          · -- n < 909352517
            rcases Nat.lt_or_ge n 909172661 with hs5 | hs5
            · -- n < 909172661
              exact Brocard.berndt_galway_chunk_5055 n m (by omega) (by omega) h
            · -- n >= 909172661
              exact Brocard.berndt_galway_chunk_5056 n m (by omega) (by omega) h
          · -- n >= 909352517
            exact Brocard.berndt_galway_chunk_5057 n m (by omega) (by omega) h
      · -- n >= 909532374
        rcases Nat.lt_or_ge n 910071942 with hs3 | hs3
        · -- n < 910071942
          rcases Nat.lt_or_ge n 909892086 with hs4 | hs4
          · -- n < 909892086
            rcases Nat.lt_or_ge n 909712230 with hs5 | hs5
            · -- n < 909712230
              exact Brocard.berndt_galway_chunk_5058 n m (by omega) (by omega) h
            · -- n >= 909712230
              exact Brocard.berndt_galway_chunk_5059 n m (by omega) (by omega) h
          · -- n >= 909892086
            exact Brocard.berndt_galway_chunk_5060 n m (by omega) (by omega) h
        · -- n >= 910071942
          rcases Nat.lt_or_ge n 910431654 with hs4 | hs4
          · -- n < 910431654
            rcases Nat.lt_or_ge n 910251798 with hs5 | hs5
            · -- n < 910251798
              exact Brocard.berndt_galway_chunk_5061 n m (by omega) (by omega) h
            · -- n >= 910251798
              exact Brocard.berndt_galway_chunk_5062 n m (by omega) (by omega) h
          · -- n >= 910431654
            exact Brocard.berndt_galway_chunk_5063 n m (by omega) (by omega) h
    · -- n >= 910611510
      rcases Nat.lt_or_ge n 911690647 with hs2 | hs2
      · -- n < 911690647
        rcases Nat.lt_or_ge n 911151079 with hs3 | hs3
        · -- n < 911151079
          rcases Nat.lt_or_ge n 910971223 with hs4 | hs4
          · -- n < 910971223
            rcases Nat.lt_or_ge n 910791366 with hs5 | hs5
            · -- n < 910791366
              exact Brocard.berndt_galway_chunk_5064 n m (by omega) (by omega) h
            · -- n >= 910791366
              exact Brocard.berndt_galway_chunk_5065 n m (by omega) (by omega) h
          · -- n >= 910971223
            exact Brocard.berndt_galway_chunk_5066 n m (by omega) (by omega) h
        · -- n >= 911151079
          rcases Nat.lt_or_ge n 911510791 with hs4 | hs4
          · -- n < 911510791
            rcases Nat.lt_or_ge n 911330935 with hs5 | hs5
            · -- n < 911330935
              exact Brocard.berndt_galway_chunk_5067 n m (by omega) (by omega) h
            · -- n >= 911330935
              exact Brocard.berndt_galway_chunk_5068 n m (by omega) (by omega) h
          · -- n >= 911510791
            exact Brocard.berndt_galway_chunk_5069 n m (by omega) (by omega) h
      · -- n >= 911690647
        rcases Nat.lt_or_ge n 912230215 with hs3 | hs3
        · -- n < 912230215
          rcases Nat.lt_or_ge n 912050359 with hs4 | hs4
          · -- n < 912050359
            rcases Nat.lt_or_ge n 911870503 with hs5 | hs5
            · -- n < 911870503
              exact Brocard.berndt_galway_chunk_5070 n m (by omega) (by omega) h
            · -- n >= 911870503
              exact Brocard.berndt_galway_chunk_5071 n m (by omega) (by omega) h
          · -- n >= 912050359
            exact Brocard.berndt_galway_chunk_5072 n m (by omega) (by omega) h
        · -- n >= 912230215
          rcases Nat.lt_or_ge n 912589928 with hs4 | hs4
          · -- n < 912589928
            rcases Nat.lt_or_ge n 912410071 with hs5 | hs5
            · -- n < 912410071
              exact Brocard.berndt_galway_chunk_5073 n m (by omega) (by omega) h
            · -- n >= 912410071
              exact Brocard.berndt_galway_chunk_5074 n m (by omega) (by omega) h
          · -- n >= 912589928
            exact Brocard.berndt_galway_chunk_5075 n m (by omega) (by omega) h
  · -- n >= 912769784
    rcases Nat.lt_or_ge n 914928057 with hs1 | hs1
    · -- n < 914928057
      rcases Nat.lt_or_ge n 913848920 with hs2 | hs2
      · -- n < 913848920
        rcases Nat.lt_or_ge n 913309352 with hs3 | hs3
        · -- n < 913309352
          rcases Nat.lt_or_ge n 913129496 with hs4 | hs4
          · -- n < 913129496
            rcases Nat.lt_or_ge n 912949640 with hs5 | hs5
            · -- n < 912949640
              exact Brocard.berndt_galway_chunk_5076 n m (by omega) (by omega) h
            · -- n >= 912949640
              exact Brocard.berndt_galway_chunk_5077 n m (by omega) (by omega) h
          · -- n >= 913129496
            exact Brocard.berndt_galway_chunk_5078 n m (by omega) (by omega) h
        · -- n >= 913309352
          rcases Nat.lt_or_ge n 913669064 with hs4 | hs4
          · -- n < 913669064
            rcases Nat.lt_or_ge n 913489208 with hs5 | hs5
            · -- n < 913489208
              exact Brocard.berndt_galway_chunk_5079 n m (by omega) (by omega) h
            · -- n >= 913489208
              exact Brocard.berndt_galway_chunk_5080 n m (by omega) (by omega) h
          · -- n >= 913669064
            exact Brocard.berndt_galway_chunk_5081 n m (by omega) (by omega) h
      · -- n >= 913848920
        rcases Nat.lt_or_ge n 914388489 with hs3 | hs3
        · -- n < 914388489
          rcases Nat.lt_or_ge n 914208633 with hs4 | hs4
          · -- n < 914208633
            rcases Nat.lt_or_ge n 914028776 with hs5 | hs5
            · -- n < 914028776
              exact Brocard.berndt_galway_chunk_5082 n m (by omega) (by omega) h
            · -- n >= 914028776
              exact Brocard.berndt_galway_chunk_5083 n m (by omega) (by omega) h
          · -- n >= 914208633
            exact Brocard.berndt_galway_chunk_5084 n m (by omega) (by omega) h
        · -- n >= 914388489
          rcases Nat.lt_or_ge n 914748201 with hs4 | hs4
          · -- n < 914748201
            rcases Nat.lt_or_ge n 914568345 with hs5 | hs5
            · -- n < 914568345
              exact Brocard.berndt_galway_chunk_5085 n m (by omega) (by omega) h
            · -- n >= 914568345
              exact Brocard.berndt_galway_chunk_5086 n m (by omega) (by omega) h
          · -- n >= 914748201
            exact Brocard.berndt_galway_chunk_5087 n m (by omega) (by omega) h
    · -- n >= 914928057
      rcases Nat.lt_or_ge n 916007194 with hs2 | hs2
      · -- n < 916007194
        rcases Nat.lt_or_ge n 915467625 with hs3 | hs3
        · -- n < 915467625
          rcases Nat.lt_or_ge n 915287769 with hs4 | hs4
          · -- n < 915287769
            rcases Nat.lt_or_ge n 915107913 with hs5 | hs5
            · -- n < 915107913
              exact Brocard.berndt_galway_chunk_5088 n m (by omega) (by omega) h
            · -- n >= 915107913
              exact Brocard.berndt_galway_chunk_5089 n m (by omega) (by omega) h
          · -- n >= 915287769
            exact Brocard.berndt_galway_chunk_5090 n m (by omega) (by omega) h
        · -- n >= 915467625
          rcases Nat.lt_or_ge n 915827338 with hs4 | hs4
          · -- n < 915827338
            rcases Nat.lt_or_ge n 915647482 with hs5 | hs5
            · -- n < 915647482
              exact Brocard.berndt_galway_chunk_5091 n m (by omega) (by omega) h
            · -- n >= 915647482
              exact Brocard.berndt_galway_chunk_5092 n m (by omega) (by omega) h
          · -- n >= 915827338
            exact Brocard.berndt_galway_chunk_5093 n m (by omega) (by omega) h
      · -- n >= 916007194
        rcases Nat.lt_or_ge n 916546762 with hs3 | hs3
        · -- n < 916546762
          rcases Nat.lt_or_ge n 916366906 with hs4 | hs4
          · -- n < 916366906
            rcases Nat.lt_or_ge n 916187050 with hs5 | hs5
            · -- n < 916187050
              exact Brocard.berndt_galway_chunk_5094 n m (by omega) (by omega) h
            · -- n >= 916187050
              exact Brocard.berndt_galway_chunk_5095 n m (by omega) (by omega) h
          · -- n >= 916366906
            exact Brocard.berndt_galway_chunk_5096 n m (by omega) (by omega) h
        · -- n >= 916546762
          rcases Nat.lt_or_ge n 916726618 with hs4 | hs4
          · -- n < 916726618
            exact Brocard.berndt_galway_chunk_5097 n m (by omega) (by omega) h
          · -- n >= 916726618
            exact Brocard.berndt_galway_chunk_5098 n m (by omega) (by omega) h
