-- Prove2me | solution 1 for Brocard.berndt_galway_group_111
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:05:03.398459+00:00
-- url     : https://prove2.me/submissions/417a61fc-7d18-4c39-9578-b0698aaf5ff9

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_5099
import Theorems.Thm_Brocard_berndt_galway_chunk_5100
import Theorems.Thm_Brocard_berndt_galway_chunk_5101
import Theorems.Thm_Brocard_berndt_galway_chunk_5102
import Theorems.Thm_Brocard_berndt_galway_chunk_5103
import Theorems.Thm_Brocard_berndt_galway_chunk_5104
import Theorems.Thm_Brocard_berndt_galway_chunk_5105
import Theorems.Thm_Brocard_berndt_galway_chunk_5106
import Theorems.Thm_Brocard_berndt_galway_chunk_5107
import Theorems.Thm_Brocard_berndt_galway_chunk_5108
import Theorems.Thm_Brocard_berndt_galway_chunk_5109
import Theorems.Thm_Brocard_berndt_galway_chunk_5110
import Theorems.Thm_Brocard_berndt_galway_chunk_5111
import Theorems.Thm_Brocard_berndt_galway_chunk_5112
import Theorems.Thm_Brocard_berndt_galway_chunk_5113
import Theorems.Thm_Brocard_berndt_galway_chunk_5114
import Theorems.Thm_Brocard_berndt_galway_chunk_5115
import Theorems.Thm_Brocard_berndt_galway_chunk_5116
import Theorems.Thm_Brocard_berndt_galway_chunk_5117
import Theorems.Thm_Brocard_berndt_galway_chunk_5118
import Theorems.Thm_Brocard_berndt_galway_chunk_5119
import Theorems.Thm_Brocard_berndt_galway_chunk_5120
import Theorems.Thm_Brocard_berndt_galway_chunk_5121
import Theorems.Thm_Brocard_berndt_galway_chunk_5122
import Theorems.Thm_Brocard_berndt_galway_chunk_5123
import Theorems.Thm_Brocard_berndt_galway_chunk_5124
import Theorems.Thm_Brocard_berndt_galway_chunk_5125
import Theorems.Thm_Brocard_berndt_galway_chunk_5126
import Theorems.Thm_Brocard_berndt_galway_chunk_5127
import Theorems.Thm_Brocard_berndt_galway_chunk_5128
import Theorems.Thm_Brocard_berndt_galway_chunk_5129
import Theorems.Thm_Brocard_berndt_galway_chunk_5130
import Theorems.Thm_Brocard_berndt_galway_chunk_5131
import Theorems.Thm_Brocard_berndt_galway_chunk_5132
import Theorems.Thm_Brocard_berndt_galway_chunk_5133
import Theorems.Thm_Brocard_berndt_galway_chunk_5134
import Theorems.Thm_Brocard_berndt_galway_chunk_5135
import Theorems.Thm_Brocard_berndt_galway_chunk_5136
import Theorems.Thm_Brocard_berndt_galway_chunk_5137
import Theorems.Thm_Brocard_berndt_galway_chunk_5138
import Theorems.Thm_Brocard_berndt_galway_chunk_5139
import Theorems.Thm_Brocard_berndt_galway_chunk_5140
import Theorems.Thm_Brocard_berndt_galway_chunk_5141
import Theorems.Thm_Brocard_berndt_galway_chunk_5142
import Theorems.Thm_Brocard_berndt_galway_chunk_5143
import Theorems.Thm_Brocard_berndt_galway_chunk_5144
import Theorems.Thm_Brocard_berndt_galway_chunk_5145

theorem solution (n m : ℕ) (h1 : 916906474 ≤ n) (h2 : n < 925359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 921223021 with hs0 | hs0
  · -- n < 921223021
    rcases Nat.lt_or_ge n 919064748 with hs1 | hs1
    · -- n < 919064748
      rcases Nat.lt_or_ge n 917985611 with hs2 | hs2
      · -- n < 917985611
        rcases Nat.lt_or_ge n 917446043 with hs3 | hs3
        · -- n < 917446043
          rcases Nat.lt_or_ge n 917266187 with hs4 | hs4
          · -- n < 917266187
            rcases Nat.lt_or_ge n 917086330 with hs5 | hs5
            · -- n < 917086330
              exact Brocard.berndt_galway_chunk_5099 n m (by omega) (by omega) h
            · -- n >= 917086330
              exact Brocard.berndt_galway_chunk_5100 n m (by omega) (by omega) h
          · -- n >= 917266187
            exact Brocard.berndt_galway_chunk_5101 n m (by omega) (by omega) h
        · -- n >= 917446043
          rcases Nat.lt_or_ge n 917805755 with hs4 | hs4
          · -- n < 917805755
            rcases Nat.lt_or_ge n 917625899 with hs5 | hs5
            · -- n < 917625899
              exact Brocard.berndt_galway_chunk_5102 n m (by omega) (by omega) h
            · -- n >= 917625899
              exact Brocard.berndt_galway_chunk_5103 n m (by omega) (by omega) h
          · -- n >= 917805755
            exact Brocard.berndt_galway_chunk_5104 n m (by omega) (by omega) h
      · -- n >= 917985611
        rcases Nat.lt_or_ge n 918525179 with hs3 | hs3
        · -- n < 918525179
          rcases Nat.lt_or_ge n 918345323 with hs4 | hs4
          · -- n < 918345323
            rcases Nat.lt_or_ge n 918165467 with hs5 | hs5
            · -- n < 918165467
              exact Brocard.berndt_galway_chunk_5105 n m (by omega) (by omega) h
            · -- n >= 918165467
              exact Brocard.berndt_galway_chunk_5106 n m (by omega) (by omega) h
          · -- n >= 918345323
            exact Brocard.berndt_galway_chunk_5107 n m (by omega) (by omega) h
        · -- n >= 918525179
          rcases Nat.lt_or_ge n 918884892 with hs4 | hs4
          · -- n < 918884892
            rcases Nat.lt_or_ge n 918705035 with hs5 | hs5
            · -- n < 918705035
              exact Brocard.berndt_galway_chunk_5108 n m (by omega) (by omega) h
            · -- n >= 918705035
              exact Brocard.berndt_galway_chunk_5109 n m (by omega) (by omega) h
          · -- n >= 918884892
            exact Brocard.berndt_galway_chunk_5110 n m (by omega) (by omega) h
    · -- n >= 919064748
      rcases Nat.lt_or_ge n 920143884 with hs2 | hs2
      · -- n < 920143884
        rcases Nat.lt_or_ge n 919604316 with hs3 | hs3
        · -- n < 919604316
          rcases Nat.lt_or_ge n 919424460 with hs4 | hs4
          · -- n < 919424460
            rcases Nat.lt_or_ge n 919244604 with hs5 | hs5
            · -- n < 919244604
              exact Brocard.berndt_galway_chunk_5111 n m (by omega) (by omega) h
            · -- n >= 919244604
              exact Brocard.berndt_galway_chunk_5112 n m (by omega) (by omega) h
          · -- n >= 919424460
            exact Brocard.berndt_galway_chunk_5113 n m (by omega) (by omega) h
        · -- n >= 919604316
          rcases Nat.lt_or_ge n 919964028 with hs4 | hs4
          · -- n < 919964028
            rcases Nat.lt_or_ge n 919784172 with hs5 | hs5
            · -- n < 919784172
              exact Brocard.berndt_galway_chunk_5114 n m (by omega) (by omega) h
            · -- n >= 919784172
              exact Brocard.berndt_galway_chunk_5115 n m (by omega) (by omega) h
          · -- n >= 919964028
            exact Brocard.berndt_galway_chunk_5116 n m (by omega) (by omega) h
      · -- n >= 920143884
        rcases Nat.lt_or_ge n 920683453 with hs3 | hs3
        · -- n < 920683453
          rcases Nat.lt_or_ge n 920503597 with hs4 | hs4
          · -- n < 920503597
            rcases Nat.lt_or_ge n 920323741 with hs5 | hs5
            · -- n < 920323741
              exact Brocard.berndt_galway_chunk_5117 n m (by omega) (by omega) h
            · -- n >= 920323741
              exact Brocard.berndt_galway_chunk_5118 n m (by omega) (by omega) h
          · -- n >= 920503597
            exact Brocard.berndt_galway_chunk_5119 n m (by omega) (by omega) h
        · -- n >= 920683453
          rcases Nat.lt_or_ge n 921043165 with hs4 | hs4
          · -- n < 921043165
            rcases Nat.lt_or_ge n 920863309 with hs5 | hs5
            · -- n < 920863309
              exact Brocard.berndt_galway_chunk_5120 n m (by omega) (by omega) h
            · -- n >= 920863309
              exact Brocard.berndt_galway_chunk_5121 n m (by omega) (by omega) h
          · -- n >= 921043165
            exact Brocard.berndt_galway_chunk_5122 n m (by omega) (by omega) h
  · -- n >= 921223021
    rcases Nat.lt_or_ge n 923381294 with hs1 | hs1
    · -- n < 923381294
      rcases Nat.lt_or_ge n 922302158 with hs2 | hs2
      · -- n < 922302158
        rcases Nat.lt_or_ge n 921762589 with hs3 | hs3
        · -- n < 921762589
          rcases Nat.lt_or_ge n 921582733 with hs4 | hs4
          · -- n < 921582733
            rcases Nat.lt_or_ge n 921402877 with hs5 | hs5
            · -- n < 921402877
              exact Brocard.berndt_galway_chunk_5123 n m (by omega) (by omega) h
            · -- n >= 921402877
              exact Brocard.berndt_galway_chunk_5124 n m (by omega) (by omega) h
          · -- n >= 921582733
            exact Brocard.berndt_galway_chunk_5125 n m (by omega) (by omega) h
        · -- n >= 921762589
          rcases Nat.lt_or_ge n 922122302 with hs4 | hs4
          · -- n < 922122302
            rcases Nat.lt_or_ge n 921942446 with hs5 | hs5
            · -- n < 921942446
              exact Brocard.berndt_galway_chunk_5126 n m (by omega) (by omega) h
            · -- n >= 921942446
              exact Brocard.berndt_galway_chunk_5127 n m (by omega) (by omega) h
          · -- n >= 922122302
            exact Brocard.berndt_galway_chunk_5128 n m (by omega) (by omega) h
      · -- n >= 922302158
        rcases Nat.lt_or_ge n 922841726 with hs3 | hs3
        · -- n < 922841726
          rcases Nat.lt_or_ge n 922661870 with hs4 | hs4
          · -- n < 922661870
            rcases Nat.lt_or_ge n 922482014 with hs5 | hs5
            · -- n < 922482014
              exact Brocard.berndt_galway_chunk_5129 n m (by omega) (by omega) h
            · -- n >= 922482014
              exact Brocard.berndt_galway_chunk_5130 n m (by omega) (by omega) h
          · -- n >= 922661870
            exact Brocard.berndt_galway_chunk_5131 n m (by omega) (by omega) h
        · -- n >= 922841726
          rcases Nat.lt_or_ge n 923201438 with hs4 | hs4
          · -- n < 923201438
            rcases Nat.lt_or_ge n 923021582 with hs5 | hs5
            · -- n < 923021582
              exact Brocard.berndt_galway_chunk_5132 n m (by omega) (by omega) h
            · -- n >= 923021582
              exact Brocard.berndt_galway_chunk_5133 n m (by omega) (by omega) h
          · -- n >= 923201438
            exact Brocard.berndt_galway_chunk_5134 n m (by omega) (by omega) h
    · -- n >= 923381294
      rcases Nat.lt_or_ge n 924460431 with hs2 | hs2
      · -- n < 924460431
        rcases Nat.lt_or_ge n 923920863 with hs3 | hs3
        · -- n < 923920863
          rcases Nat.lt_or_ge n 923741007 with hs4 | hs4
          · -- n < 923741007
            rcases Nat.lt_or_ge n 923561151 with hs5 | hs5
            · -- n < 923561151
              exact Brocard.berndt_galway_chunk_5135 n m (by omega) (by omega) h
            · -- n >= 923561151
              exact Brocard.berndt_galway_chunk_5136 n m (by omega) (by omega) h
          · -- n >= 923741007
            exact Brocard.berndt_galway_chunk_5137 n m (by omega) (by omega) h
        · -- n >= 923920863
          rcases Nat.lt_or_ge n 924280575 with hs4 | hs4
          · -- n < 924280575
            rcases Nat.lt_or_ge n 924100719 with hs5 | hs5
            · -- n < 924100719
              exact Brocard.berndt_galway_chunk_5138 n m (by omega) (by omega) h
            · -- n >= 924100719
              exact Brocard.berndt_galway_chunk_5139 n m (by omega) (by omega) h
          · -- n >= 924280575
            exact Brocard.berndt_galway_chunk_5140 n m (by omega) (by omega) h
      · -- n >= 924460431
        rcases Nat.lt_or_ge n 925000000 with hs3 | hs3
        · -- n < 925000000
          rcases Nat.lt_or_ge n 924820143 with hs4 | hs4
          · -- n < 924820143
            rcases Nat.lt_or_ge n 924640287 with hs5 | hs5
            · -- n < 924640287
              exact Brocard.berndt_galway_chunk_5141 n m (by omega) (by omega) h
            · -- n >= 924640287
              exact Brocard.berndt_galway_chunk_5142 n m (by omega) (by omega) h
          · -- n >= 924820143
            exact Brocard.berndt_galway_chunk_5143 n m (by omega) (by omega) h
        · -- n >= 925000000
          rcases Nat.lt_or_ge n 925179856 with hs4 | hs4
          · -- n < 925179856
            exact Brocard.berndt_galway_chunk_5144 n m (by omega) (by omega) h
          · -- n >= 925179856
            exact Brocard.berndt_galway_chunk_5145 n m (by omega) (by omega) h
