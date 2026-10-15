-- Prove2me | solution 1 for Brocard.berndt_galway_group_089
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:45:32.84842+00:00
-- url     : https://prove2.me/submissions/11e3d348-7753-4d03-8524-622ad3be6796

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_4081
import Theorems.Thm_Brocard_berndt_galway_chunk_4082
import Theorems.Thm_Brocard_berndt_galway_chunk_4083
import Theorems.Thm_Brocard_berndt_galway_chunk_4084
import Theorems.Thm_Brocard_berndt_galway_chunk_4085
import Theorems.Thm_Brocard_berndt_galway_chunk_4086
import Theorems.Thm_Brocard_berndt_galway_chunk_4087
import Theorems.Thm_Brocard_berndt_galway_chunk_4088
import Theorems.Thm_Brocard_berndt_galway_chunk_4089
import Theorems.Thm_Brocard_berndt_galway_chunk_4090
import Theorems.Thm_Brocard_berndt_galway_chunk_4091
import Theorems.Thm_Brocard_berndt_galway_chunk_4092
import Theorems.Thm_Brocard_berndt_galway_chunk_4093
import Theorems.Thm_Brocard_berndt_galway_chunk_4094
import Theorems.Thm_Brocard_berndt_galway_chunk_4095
import Theorems.Thm_Brocard_berndt_galway_chunk_4096
import Theorems.Thm_Brocard_berndt_galway_chunk_4097
import Theorems.Thm_Brocard_berndt_galway_chunk_4098
import Theorems.Thm_Brocard_berndt_galway_chunk_4099
import Theorems.Thm_Brocard_berndt_galway_chunk_4100
import Theorems.Thm_Brocard_berndt_galway_chunk_4101
import Theorems.Thm_Brocard_berndt_galway_chunk_4102
import Theorems.Thm_Brocard_berndt_galway_chunk_4103
import Theorems.Thm_Brocard_berndt_galway_chunk_4104
import Theorems.Thm_Brocard_berndt_galway_chunk_4105
import Theorems.Thm_Brocard_berndt_galway_chunk_4106
import Theorems.Thm_Brocard_berndt_galway_chunk_4107
import Theorems.Thm_Brocard_berndt_galway_chunk_4108
import Theorems.Thm_Brocard_berndt_galway_chunk_4109
import Theorems.Thm_Brocard_berndt_galway_chunk_4110
import Theorems.Thm_Brocard_berndt_galway_chunk_4111
import Theorems.Thm_Brocard_berndt_galway_chunk_4112
import Theorems.Thm_Brocard_berndt_galway_chunk_4113
import Theorems.Thm_Brocard_berndt_galway_chunk_4114
import Theorems.Thm_Brocard_berndt_galway_chunk_4115
import Theorems.Thm_Brocard_berndt_galway_chunk_4116
import Theorems.Thm_Brocard_berndt_galway_chunk_4117
import Theorems.Thm_Brocard_berndt_galway_chunk_4118
import Theorems.Thm_Brocard_berndt_galway_chunk_4119
import Theorems.Thm_Brocard_berndt_galway_chunk_4120
import Theorems.Thm_Brocard_berndt_galway_chunk_4121
import Theorems.Thm_Brocard_berndt_galway_chunk_4122
import Theorems.Thm_Brocard_berndt_galway_chunk_4123
import Theorems.Thm_Brocard_berndt_galway_chunk_4124
import Theorems.Thm_Brocard_berndt_galway_chunk_4125
import Theorems.Thm_Brocard_berndt_galway_chunk_4126

theorem solution (n m : ℕ) (h1 : 733812949 ≤ n) (h2 : n < 742086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 737949640 with hs0 | hs0
  · -- n < 737949640
    rcases Nat.lt_or_ge n 735971223 with hs1 | hs1
    · -- n < 735971223
      rcases Nat.lt_or_ge n 734892086 with hs2 | hs2
      · -- n < 734892086
        rcases Nat.lt_or_ge n 734352517 with hs3 | hs3
        · -- n < 734352517
          rcases Nat.lt_or_ge n 734172661 with hs4 | hs4
          · -- n < 734172661
            rcases Nat.lt_or_ge n 733992805 with hs5 | hs5
            · -- n < 733992805
              exact Brocard.berndt_galway_chunk_4081 n m (by omega) (by omega) h
            · -- n >= 733992805
              exact Brocard.berndt_galway_chunk_4082 n m (by omega) (by omega) h
          · -- n >= 734172661
            exact Brocard.berndt_galway_chunk_4083 n m (by omega) (by omega) h
        · -- n >= 734352517
          rcases Nat.lt_or_ge n 734712230 with hs4 | hs4
          · -- n < 734712230
            rcases Nat.lt_or_ge n 734532374 with hs5 | hs5
            · -- n < 734532374
              exact Brocard.berndt_galway_chunk_4084 n m (by omega) (by omega) h
            · -- n >= 734532374
              exact Brocard.berndt_galway_chunk_4085 n m (by omega) (by omega) h
          · -- n >= 734712230
            exact Brocard.berndt_galway_chunk_4086 n m (by omega) (by omega) h
      · -- n >= 734892086
        rcases Nat.lt_or_ge n 735431654 with hs3 | hs3
        · -- n < 735431654
          rcases Nat.lt_or_ge n 735251798 with hs4 | hs4
          · -- n < 735251798
            rcases Nat.lt_or_ge n 735071942 with hs5 | hs5
            · -- n < 735071942
              exact Brocard.berndt_galway_chunk_4087 n m (by omega) (by omega) h
            · -- n >= 735071942
              exact Brocard.berndt_galway_chunk_4088 n m (by omega) (by omega) h
          · -- n >= 735251798
            exact Brocard.berndt_galway_chunk_4089 n m (by omega) (by omega) h
        · -- n >= 735431654
          rcases Nat.lt_or_ge n 735791366 with hs4 | hs4
          · -- n < 735791366
            rcases Nat.lt_or_ge n 735611510 with hs5 | hs5
            · -- n < 735611510
              exact Brocard.berndt_galway_chunk_4090 n m (by omega) (by omega) h
            · -- n >= 735611510
              exact Brocard.berndt_galway_chunk_4091 n m (by omega) (by omega) h
          · -- n >= 735791366
            exact Brocard.berndt_galway_chunk_4092 n m (by omega) (by omega) h
    · -- n >= 735971223
      rcases Nat.lt_or_ge n 737050359 with hs2 | hs2
      · -- n < 737050359
        rcases Nat.lt_or_ge n 736510791 with hs3 | hs3
        · -- n < 736510791
          rcases Nat.lt_or_ge n 736330935 with hs4 | hs4
          · -- n < 736330935
            rcases Nat.lt_or_ge n 736151079 with hs5 | hs5
            · -- n < 736151079
              exact Brocard.berndt_galway_chunk_4093 n m (by omega) (by omega) h
            · -- n >= 736151079
              exact Brocard.berndt_galway_chunk_4094 n m (by omega) (by omega) h
          · -- n >= 736330935
            exact Brocard.berndt_galway_chunk_4095 n m (by omega) (by omega) h
        · -- n >= 736510791
          rcases Nat.lt_or_ge n 736870503 with hs4 | hs4
          · -- n < 736870503
            rcases Nat.lt_or_ge n 736690647 with hs5 | hs5
            · -- n < 736690647
              exact Brocard.berndt_galway_chunk_4096 n m (by omega) (by omega) h
            · -- n >= 736690647
              exact Brocard.berndt_galway_chunk_4097 n m (by omega) (by omega) h
          · -- n >= 736870503
            exact Brocard.berndt_galway_chunk_4098 n m (by omega) (by omega) h
      · -- n >= 737050359
        rcases Nat.lt_or_ge n 737589928 with hs3 | hs3
        · -- n < 737589928
          rcases Nat.lt_or_ge n 737410071 with hs4 | hs4
          · -- n < 737410071
            rcases Nat.lt_or_ge n 737230215 with hs5 | hs5
            · -- n < 737230215
              exact Brocard.berndt_galway_chunk_4099 n m (by omega) (by omega) h
            · -- n >= 737230215
              exact Brocard.berndt_galway_chunk_4100 n m (by omega) (by omega) h
          · -- n >= 737410071
            exact Brocard.berndt_galway_chunk_4101 n m (by omega) (by omega) h
        · -- n >= 737589928
          rcases Nat.lt_or_ge n 737769784 with hs4 | hs4
          · -- n < 737769784
            exact Brocard.berndt_galway_chunk_4102 n m (by omega) (by omega) h
          · -- n >= 737769784
            exact Brocard.berndt_galway_chunk_4103 n m (by omega) (by omega) h
  · -- n >= 737949640
    rcases Nat.lt_or_ge n 740107913 with hs1 | hs1
    · -- n < 740107913
      rcases Nat.lt_or_ge n 739028776 with hs2 | hs2
      · -- n < 739028776
        rcases Nat.lt_or_ge n 738489208 with hs3 | hs3
        · -- n < 738489208
          rcases Nat.lt_or_ge n 738309352 with hs4 | hs4
          · -- n < 738309352
            rcases Nat.lt_or_ge n 738129496 with hs5 | hs5
            · -- n < 738129496
              exact Brocard.berndt_galway_chunk_4104 n m (by omega) (by omega) h
            · -- n >= 738129496
              exact Brocard.berndt_galway_chunk_4105 n m (by omega) (by omega) h
          · -- n >= 738309352
            exact Brocard.berndt_galway_chunk_4106 n m (by omega) (by omega) h
        · -- n >= 738489208
          rcases Nat.lt_or_ge n 738848920 with hs4 | hs4
          · -- n < 738848920
            rcases Nat.lt_or_ge n 738669064 with hs5 | hs5
            · -- n < 738669064
              exact Brocard.berndt_galway_chunk_4107 n m (by omega) (by omega) h
            · -- n >= 738669064
              exact Brocard.berndt_galway_chunk_4108 n m (by omega) (by omega) h
          · -- n >= 738848920
            exact Brocard.berndt_galway_chunk_4109 n m (by omega) (by omega) h
      · -- n >= 739028776
        rcases Nat.lt_or_ge n 739568345 with hs3 | hs3
        · -- n < 739568345
          rcases Nat.lt_or_ge n 739388489 with hs4 | hs4
          · -- n < 739388489
            rcases Nat.lt_or_ge n 739208633 with hs5 | hs5
            · -- n < 739208633
              exact Brocard.berndt_galway_chunk_4110 n m (by omega) (by omega) h
            · -- n >= 739208633
              exact Brocard.berndt_galway_chunk_4111 n m (by omega) (by omega) h
          · -- n >= 739388489
            exact Brocard.berndt_galway_chunk_4112 n m (by omega) (by omega) h
        · -- n >= 739568345
          rcases Nat.lt_or_ge n 739928057 with hs4 | hs4
          · -- n < 739928057
            rcases Nat.lt_or_ge n 739748201 with hs5 | hs5
            · -- n < 739748201
              exact Brocard.berndt_galway_chunk_4113 n m (by omega) (by omega) h
            · -- n >= 739748201
              exact Brocard.berndt_galway_chunk_4114 n m (by omega) (by omega) h
          · -- n >= 739928057
            exact Brocard.berndt_galway_chunk_4115 n m (by omega) (by omega) h
    · -- n >= 740107913
      rcases Nat.lt_or_ge n 741187050 with hs2 | hs2
      · -- n < 741187050
        rcases Nat.lt_or_ge n 740647482 with hs3 | hs3
        · -- n < 740647482
          rcases Nat.lt_or_ge n 740467625 with hs4 | hs4
          · -- n < 740467625
            rcases Nat.lt_or_ge n 740287769 with hs5 | hs5
            · -- n < 740287769
              exact Brocard.berndt_galway_chunk_4116 n m (by omega) (by omega) h
            · -- n >= 740287769
              exact Brocard.berndt_galway_chunk_4117 n m (by omega) (by omega) h
          · -- n >= 740467625
            exact Brocard.berndt_galway_chunk_4118 n m (by omega) (by omega) h
        · -- n >= 740647482
          rcases Nat.lt_or_ge n 741007194 with hs4 | hs4
          · -- n < 741007194
            rcases Nat.lt_or_ge n 740827338 with hs5 | hs5
            · -- n < 740827338
              exact Brocard.berndt_galway_chunk_4119 n m (by omega) (by omega) h
            · -- n >= 740827338
              exact Brocard.berndt_galway_chunk_4120 n m (by omega) (by omega) h
          · -- n >= 741007194
            exact Brocard.berndt_galway_chunk_4121 n m (by omega) (by omega) h
      · -- n >= 741187050
        rcases Nat.lt_or_ge n 741726618 with hs3 | hs3
        · -- n < 741726618
          rcases Nat.lt_or_ge n 741546762 with hs4 | hs4
          · -- n < 741546762
            rcases Nat.lt_or_ge n 741366906 with hs5 | hs5
            · -- n < 741366906
              exact Brocard.berndt_galway_chunk_4122 n m (by omega) (by omega) h
            · -- n >= 741366906
              exact Brocard.berndt_galway_chunk_4123 n m (by omega) (by omega) h
          · -- n >= 741546762
            exact Brocard.berndt_galway_chunk_4124 n m (by omega) (by omega) h
        · -- n >= 741726618
          rcases Nat.lt_or_ge n 741906474 with hs4 | hs4
          · -- n < 741906474
            exact Brocard.berndt_galway_chunk_4125 n m (by omega) (by omega) h
          · -- n >= 741906474
            exact Brocard.berndt_galway_chunk_4126 n m (by omega) (by omega) h
