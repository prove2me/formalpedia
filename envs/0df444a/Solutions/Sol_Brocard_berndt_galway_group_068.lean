-- Prove2me | solution 1 for Brocard.berndt_galway_group_068
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:53:57.459807+00:00
-- url     : https://prove2.me/submissions/d7166709-13eb-4385-b24b-8fa858a23e55

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_3107
import Theorems.Thm_Brocard_berndt_galway_chunk_3108
import Theorems.Thm_Brocard_berndt_galway_chunk_3109
import Theorems.Thm_Brocard_berndt_galway_chunk_3110
import Theorems.Thm_Brocard_berndt_galway_chunk_3111
import Theorems.Thm_Brocard_berndt_galway_chunk_3112
import Theorems.Thm_Brocard_berndt_galway_chunk_3113
import Theorems.Thm_Brocard_berndt_galway_chunk_3114
import Theorems.Thm_Brocard_berndt_galway_chunk_3115
import Theorems.Thm_Brocard_berndt_galway_chunk_3116
import Theorems.Thm_Brocard_berndt_galway_chunk_3117
import Theorems.Thm_Brocard_berndt_galway_chunk_3118
import Theorems.Thm_Brocard_berndt_galway_chunk_3119
import Theorems.Thm_Brocard_berndt_galway_chunk_3120
import Theorems.Thm_Brocard_berndt_galway_chunk_3121
import Theorems.Thm_Brocard_berndt_galway_chunk_3122
import Theorems.Thm_Brocard_berndt_galway_chunk_3123
import Theorems.Thm_Brocard_berndt_galway_chunk_3124
import Theorems.Thm_Brocard_berndt_galway_chunk_3125
import Theorems.Thm_Brocard_berndt_galway_chunk_3126
import Theorems.Thm_Brocard_berndt_galway_chunk_3127
import Theorems.Thm_Brocard_berndt_galway_chunk_3128
import Theorems.Thm_Brocard_berndt_galway_chunk_3129
import Theorems.Thm_Brocard_berndt_galway_chunk_3130
import Theorems.Thm_Brocard_berndt_galway_chunk_3131
import Theorems.Thm_Brocard_berndt_galway_chunk_3132
import Theorems.Thm_Brocard_berndt_galway_chunk_3133
import Theorems.Thm_Brocard_berndt_galway_chunk_3134
import Theorems.Thm_Brocard_berndt_galway_chunk_3135
import Theorems.Thm_Brocard_berndt_galway_chunk_3136
import Theorems.Thm_Brocard_berndt_galway_chunk_3137
import Theorems.Thm_Brocard_berndt_galway_chunk_3138
import Theorems.Thm_Brocard_berndt_galway_chunk_3139
import Theorems.Thm_Brocard_berndt_galway_chunk_3140
import Theorems.Thm_Brocard_berndt_galway_chunk_3141
import Theorems.Thm_Brocard_berndt_galway_chunk_3142
import Theorems.Thm_Brocard_berndt_galway_chunk_3143
import Theorems.Thm_Brocard_berndt_galway_chunk_3144
import Theorems.Thm_Brocard_berndt_galway_chunk_3145
import Theorems.Thm_Brocard_berndt_galway_chunk_3146
import Theorems.Thm_Brocard_berndt_galway_chunk_3147
import Theorems.Thm_Brocard_berndt_galway_chunk_3148
import Theorems.Thm_Brocard_berndt_galway_chunk_3149
import Theorems.Thm_Brocard_berndt_galway_chunk_3150
import Theorems.Thm_Brocard_berndt_galway_chunk_3151
import Theorems.Thm_Brocard_berndt_galway_chunk_3152

theorem solution (n m : ℕ) (h1 : 558633093 ≤ n) (h2 : n < 566906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 562769784 with hs0 | hs0
  · -- n < 562769784
    rcases Nat.lt_or_ge n 560791366 with hs1 | hs1
    · -- n < 560791366
      rcases Nat.lt_or_ge n 559712230 with hs2 | hs2
      · -- n < 559712230
        rcases Nat.lt_or_ge n 559172661 with hs3 | hs3
        · -- n < 559172661
          rcases Nat.lt_or_ge n 558992805 with hs4 | hs4
          · -- n < 558992805
            rcases Nat.lt_or_ge n 558812949 with hs5 | hs5
            · -- n < 558812949
              exact Brocard.berndt_galway_chunk_3107 n m (by omega) (by omega) h
            · -- n >= 558812949
              exact Brocard.berndt_galway_chunk_3108 n m (by omega) (by omega) h
          · -- n >= 558992805
            exact Brocard.berndt_galway_chunk_3109 n m (by omega) (by omega) h
        · -- n >= 559172661
          rcases Nat.lt_or_ge n 559532374 with hs4 | hs4
          · -- n < 559532374
            rcases Nat.lt_or_ge n 559352517 with hs5 | hs5
            · -- n < 559352517
              exact Brocard.berndt_galway_chunk_3110 n m (by omega) (by omega) h
            · -- n >= 559352517
              exact Brocard.berndt_galway_chunk_3111 n m (by omega) (by omega) h
          · -- n >= 559532374
            exact Brocard.berndt_galway_chunk_3112 n m (by omega) (by omega) h
      · -- n >= 559712230
        rcases Nat.lt_or_ge n 560251798 with hs3 | hs3
        · -- n < 560251798
          rcases Nat.lt_or_ge n 560071942 with hs4 | hs4
          · -- n < 560071942
            rcases Nat.lt_or_ge n 559892086 with hs5 | hs5
            · -- n < 559892086
              exact Brocard.berndt_galway_chunk_3113 n m (by omega) (by omega) h
            · -- n >= 559892086
              exact Brocard.berndt_galway_chunk_3114 n m (by omega) (by omega) h
          · -- n >= 560071942
            exact Brocard.berndt_galway_chunk_3115 n m (by omega) (by omega) h
        · -- n >= 560251798
          rcases Nat.lt_or_ge n 560611510 with hs4 | hs4
          · -- n < 560611510
            rcases Nat.lt_or_ge n 560431654 with hs5 | hs5
            · -- n < 560431654
              exact Brocard.berndt_galway_chunk_3116 n m (by omega) (by omega) h
            · -- n >= 560431654
              exact Brocard.berndt_galway_chunk_3117 n m (by omega) (by omega) h
          · -- n >= 560611510
            exact Brocard.berndt_galway_chunk_3118 n m (by omega) (by omega) h
    · -- n >= 560791366
      rcases Nat.lt_or_ge n 561870503 with hs2 | hs2
      · -- n < 561870503
        rcases Nat.lt_or_ge n 561330935 with hs3 | hs3
        · -- n < 561330935
          rcases Nat.lt_or_ge n 561151079 with hs4 | hs4
          · -- n < 561151079
            rcases Nat.lt_or_ge n 560971223 with hs5 | hs5
            · -- n < 560971223
              exact Brocard.berndt_galway_chunk_3119 n m (by omega) (by omega) h
            · -- n >= 560971223
              exact Brocard.berndt_galway_chunk_3120 n m (by omega) (by omega) h
          · -- n >= 561151079
            exact Brocard.berndt_galway_chunk_3121 n m (by omega) (by omega) h
        · -- n >= 561330935
          rcases Nat.lt_or_ge n 561690647 with hs4 | hs4
          · -- n < 561690647
            rcases Nat.lt_or_ge n 561510791 with hs5 | hs5
            · -- n < 561510791
              exact Brocard.berndt_galway_chunk_3122 n m (by omega) (by omega) h
            · -- n >= 561510791
              exact Brocard.berndt_galway_chunk_3123 n m (by omega) (by omega) h
          · -- n >= 561690647
            exact Brocard.berndt_galway_chunk_3124 n m (by omega) (by omega) h
      · -- n >= 561870503
        rcases Nat.lt_or_ge n 562410071 with hs3 | hs3
        · -- n < 562410071
          rcases Nat.lt_or_ge n 562230215 with hs4 | hs4
          · -- n < 562230215
            rcases Nat.lt_or_ge n 562050359 with hs5 | hs5
            · -- n < 562050359
              exact Brocard.berndt_galway_chunk_3125 n m (by omega) (by omega) h
            · -- n >= 562050359
              exact Brocard.berndt_galway_chunk_3126 n m (by omega) (by omega) h
          · -- n >= 562230215
            exact Brocard.berndt_galway_chunk_3127 n m (by omega) (by omega) h
        · -- n >= 562410071
          rcases Nat.lt_or_ge n 562589928 with hs4 | hs4
          · -- n < 562589928
            exact Brocard.berndt_galway_chunk_3128 n m (by omega) (by omega) h
          · -- n >= 562589928
            exact Brocard.berndt_galway_chunk_3129 n m (by omega) (by omega) h
  · -- n >= 562769784
    rcases Nat.lt_or_ge n 564928057 with hs1 | hs1
    · -- n < 564928057
      rcases Nat.lt_or_ge n 563848920 with hs2 | hs2
      · -- n < 563848920
        rcases Nat.lt_or_ge n 563309352 with hs3 | hs3
        · -- n < 563309352
          rcases Nat.lt_or_ge n 563129496 with hs4 | hs4
          · -- n < 563129496
            rcases Nat.lt_or_ge n 562949640 with hs5 | hs5
            · -- n < 562949640
              exact Brocard.berndt_galway_chunk_3130 n m (by omega) (by omega) h
            · -- n >= 562949640
              exact Brocard.berndt_galway_chunk_3131 n m (by omega) (by omega) h
          · -- n >= 563129496
            exact Brocard.berndt_galway_chunk_3132 n m (by omega) (by omega) h
        · -- n >= 563309352
          rcases Nat.lt_or_ge n 563669064 with hs4 | hs4
          · -- n < 563669064
            rcases Nat.lt_or_ge n 563489208 with hs5 | hs5
            · -- n < 563489208
              exact Brocard.berndt_galway_chunk_3133 n m (by omega) (by omega) h
            · -- n >= 563489208
              exact Brocard.berndt_galway_chunk_3134 n m (by omega) (by omega) h
          · -- n >= 563669064
            exact Brocard.berndt_galway_chunk_3135 n m (by omega) (by omega) h
      · -- n >= 563848920
        rcases Nat.lt_or_ge n 564388489 with hs3 | hs3
        · -- n < 564388489
          rcases Nat.lt_or_ge n 564208633 with hs4 | hs4
          · -- n < 564208633
            rcases Nat.lt_or_ge n 564028776 with hs5 | hs5
            · -- n < 564028776
              exact Brocard.berndt_galway_chunk_3136 n m (by omega) (by omega) h
            · -- n >= 564028776
              exact Brocard.berndt_galway_chunk_3137 n m (by omega) (by omega) h
          · -- n >= 564208633
            exact Brocard.berndt_galway_chunk_3138 n m (by omega) (by omega) h
        · -- n >= 564388489
          rcases Nat.lt_or_ge n 564748201 with hs4 | hs4
          · -- n < 564748201
            rcases Nat.lt_or_ge n 564568345 with hs5 | hs5
            · -- n < 564568345
              exact Brocard.berndt_galway_chunk_3139 n m (by omega) (by omega) h
            · -- n >= 564568345
              exact Brocard.berndt_galway_chunk_3140 n m (by omega) (by omega) h
          · -- n >= 564748201
            exact Brocard.berndt_galway_chunk_3141 n m (by omega) (by omega) h
    · -- n >= 564928057
      rcases Nat.lt_or_ge n 566007194 with hs2 | hs2
      · -- n < 566007194
        rcases Nat.lt_or_ge n 565467625 with hs3 | hs3
        · -- n < 565467625
          rcases Nat.lt_or_ge n 565287769 with hs4 | hs4
          · -- n < 565287769
            rcases Nat.lt_or_ge n 565107913 with hs5 | hs5
            · -- n < 565107913
              exact Brocard.berndt_galway_chunk_3142 n m (by omega) (by omega) h
            · -- n >= 565107913
              exact Brocard.berndt_galway_chunk_3143 n m (by omega) (by omega) h
          · -- n >= 565287769
            exact Brocard.berndt_galway_chunk_3144 n m (by omega) (by omega) h
        · -- n >= 565467625
          rcases Nat.lt_or_ge n 565827338 with hs4 | hs4
          · -- n < 565827338
            rcases Nat.lt_or_ge n 565647482 with hs5 | hs5
            · -- n < 565647482
              exact Brocard.berndt_galway_chunk_3145 n m (by omega) (by omega) h
            · -- n >= 565647482
              exact Brocard.berndt_galway_chunk_3146 n m (by omega) (by omega) h
          · -- n >= 565827338
            exact Brocard.berndt_galway_chunk_3147 n m (by omega) (by omega) h
      · -- n >= 566007194
        rcases Nat.lt_or_ge n 566546762 with hs3 | hs3
        · -- n < 566546762
          rcases Nat.lt_or_ge n 566366906 with hs4 | hs4
          · -- n < 566366906
            rcases Nat.lt_or_ge n 566187050 with hs5 | hs5
            · -- n < 566187050
              exact Brocard.berndt_galway_chunk_3148 n m (by omega) (by omega) h
            · -- n >= 566187050
              exact Brocard.berndt_galway_chunk_3149 n m (by omega) (by omega) h
          · -- n >= 566366906
            exact Brocard.berndt_galway_chunk_3150 n m (by omega) (by omega) h
        · -- n >= 566546762
          rcases Nat.lt_or_ge n 566726618 with hs4 | hs4
          · -- n < 566726618
            exact Brocard.berndt_galway_chunk_3151 n m (by omega) (by omega) h
          · -- n >= 566726618
            exact Brocard.berndt_galway_chunk_3152 n m (by omega) (by omega) h
