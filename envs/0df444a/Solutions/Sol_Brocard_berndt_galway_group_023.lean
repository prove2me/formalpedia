-- Prove2me | solution 1 for Brocard.berndt_galway_group_023
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:11:59.537925+00:00
-- url     : https://prove2.me/submissions/a3efd6ba-cc06-4c64-8af0-75541dc83b99

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_1021
import Theorems.Thm_Brocard_berndt_galway_chunk_1022
import Theorems.Thm_Brocard_berndt_galway_chunk_1023
import Theorems.Thm_Brocard_berndt_galway_chunk_1024
import Theorems.Thm_Brocard_berndt_galway_chunk_1025
import Theorems.Thm_Brocard_berndt_galway_chunk_1026
import Theorems.Thm_Brocard_berndt_galway_chunk_1027
import Theorems.Thm_Brocard_berndt_galway_chunk_1028
import Theorems.Thm_Brocard_berndt_galway_chunk_1029
import Theorems.Thm_Brocard_berndt_galway_chunk_1030
import Theorems.Thm_Brocard_berndt_galway_chunk_1031
import Theorems.Thm_Brocard_berndt_galway_chunk_1032
import Theorems.Thm_Brocard_berndt_galway_chunk_1033
import Theorems.Thm_Brocard_berndt_galway_chunk_1034
import Theorems.Thm_Brocard_berndt_galway_chunk_1035
import Theorems.Thm_Brocard_berndt_galway_chunk_1036
import Theorems.Thm_Brocard_berndt_galway_chunk_1037
import Theorems.Thm_Brocard_berndt_galway_chunk_1038
import Theorems.Thm_Brocard_berndt_galway_chunk_1039
import Theorems.Thm_Brocard_berndt_galway_chunk_1040
import Theorems.Thm_Brocard_berndt_galway_chunk_1041
import Theorems.Thm_Brocard_berndt_galway_chunk_1042
import Theorems.Thm_Brocard_berndt_galway_chunk_1043
import Theorems.Thm_Brocard_berndt_galway_chunk_1044
import Theorems.Thm_Brocard_berndt_galway_chunk_1045
import Theorems.Thm_Brocard_berndt_galway_chunk_1046
import Theorems.Thm_Brocard_berndt_galway_chunk_1047
import Theorems.Thm_Brocard_berndt_galway_chunk_1048
import Theorems.Thm_Brocard_berndt_galway_chunk_1049
import Theorems.Thm_Brocard_berndt_galway_chunk_1050
import Theorems.Thm_Brocard_berndt_galway_chunk_1051
import Theorems.Thm_Brocard_berndt_galway_chunk_1052
import Theorems.Thm_Brocard_berndt_galway_chunk_1053
import Theorems.Thm_Brocard_berndt_galway_chunk_1054
import Theorems.Thm_Brocard_berndt_galway_chunk_1055
import Theorems.Thm_Brocard_berndt_galway_chunk_1056
import Theorems.Thm_Brocard_berndt_galway_chunk_1057
import Theorems.Thm_Brocard_berndt_galway_chunk_1058
import Theorems.Thm_Brocard_berndt_galway_chunk_1059
import Theorems.Thm_Brocard_berndt_galway_chunk_1060
import Theorems.Thm_Brocard_berndt_galway_chunk_1061
import Theorems.Thm_Brocard_berndt_galway_chunk_1062
import Theorems.Thm_Brocard_berndt_galway_chunk_1063
import Theorems.Thm_Brocard_berndt_galway_chunk_1064
import Theorems.Thm_Brocard_berndt_galway_chunk_1065
import Theorems.Thm_Brocard_berndt_galway_chunk_1066

theorem solution (n m : ℕ) (h1 : 183453237 ≤ n) (h2 : n < 191726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 187589928 with hs0 | hs0
  · -- n < 187589928
    rcases Nat.lt_or_ge n 185611510 with hs1 | hs1
    · -- n < 185611510
      rcases Nat.lt_or_ge n 184532374 with hs2 | hs2
      · -- n < 184532374
        rcases Nat.lt_or_ge n 183992805 with hs3 | hs3
        · -- n < 183992805
          rcases Nat.lt_or_ge n 183812949 with hs4 | hs4
          · -- n < 183812949
            rcases Nat.lt_or_ge n 183633093 with hs5 | hs5
            · -- n < 183633093
              exact Brocard.berndt_galway_chunk_1021 n m (by omega) (by omega) h
            · -- n >= 183633093
              exact Brocard.berndt_galway_chunk_1022 n m (by omega) (by omega) h
          · -- n >= 183812949
            exact Brocard.berndt_galway_chunk_1023 n m (by omega) (by omega) h
        · -- n >= 183992805
          rcases Nat.lt_or_ge n 184352517 with hs4 | hs4
          · -- n < 184352517
            rcases Nat.lt_or_ge n 184172661 with hs5 | hs5
            · -- n < 184172661
              exact Brocard.berndt_galway_chunk_1024 n m (by omega) (by omega) h
            · -- n >= 184172661
              exact Brocard.berndt_galway_chunk_1025 n m (by omega) (by omega) h
          · -- n >= 184352517
            exact Brocard.berndt_galway_chunk_1026 n m (by omega) (by omega) h
      · -- n >= 184532374
        rcases Nat.lt_or_ge n 185071942 with hs3 | hs3
        · -- n < 185071942
          rcases Nat.lt_or_ge n 184892086 with hs4 | hs4
          · -- n < 184892086
            rcases Nat.lt_or_ge n 184712230 with hs5 | hs5
            · -- n < 184712230
              exact Brocard.berndt_galway_chunk_1027 n m (by omega) (by omega) h
            · -- n >= 184712230
              exact Brocard.berndt_galway_chunk_1028 n m (by omega) (by omega) h
          · -- n >= 184892086
            exact Brocard.berndt_galway_chunk_1029 n m (by omega) (by omega) h
        · -- n >= 185071942
          rcases Nat.lt_or_ge n 185431654 with hs4 | hs4
          · -- n < 185431654
            rcases Nat.lt_or_ge n 185251798 with hs5 | hs5
            · -- n < 185251798
              exact Brocard.berndt_galway_chunk_1030 n m (by omega) (by omega) h
            · -- n >= 185251798
              exact Brocard.berndt_galway_chunk_1031 n m (by omega) (by omega) h
          · -- n >= 185431654
            exact Brocard.berndt_galway_chunk_1032 n m (by omega) (by omega) h
    · -- n >= 185611510
      rcases Nat.lt_or_ge n 186690647 with hs2 | hs2
      · -- n < 186690647
        rcases Nat.lt_or_ge n 186151079 with hs3 | hs3
        · -- n < 186151079
          rcases Nat.lt_or_ge n 185971223 with hs4 | hs4
          · -- n < 185971223
            rcases Nat.lt_or_ge n 185791366 with hs5 | hs5
            · -- n < 185791366
              exact Brocard.berndt_galway_chunk_1033 n m (by omega) (by omega) h
            · -- n >= 185791366
              exact Brocard.berndt_galway_chunk_1034 n m (by omega) (by omega) h
          · -- n >= 185971223
            exact Brocard.berndt_galway_chunk_1035 n m (by omega) (by omega) h
        · -- n >= 186151079
          rcases Nat.lt_or_ge n 186510791 with hs4 | hs4
          · -- n < 186510791
            rcases Nat.lt_or_ge n 186330935 with hs5 | hs5
            · -- n < 186330935
              exact Brocard.berndt_galway_chunk_1036 n m (by omega) (by omega) h
            · -- n >= 186330935
              exact Brocard.berndt_galway_chunk_1037 n m (by omega) (by omega) h
          · -- n >= 186510791
            exact Brocard.berndt_galway_chunk_1038 n m (by omega) (by omega) h
      · -- n >= 186690647
        rcases Nat.lt_or_ge n 187230215 with hs3 | hs3
        · -- n < 187230215
          rcases Nat.lt_or_ge n 187050359 with hs4 | hs4
          · -- n < 187050359
            rcases Nat.lt_or_ge n 186870503 with hs5 | hs5
            · -- n < 186870503
              exact Brocard.berndt_galway_chunk_1039 n m (by omega) (by omega) h
            · -- n >= 186870503
              exact Brocard.berndt_galway_chunk_1040 n m (by omega) (by omega) h
          · -- n >= 187050359
            exact Brocard.berndt_galway_chunk_1041 n m (by omega) (by omega) h
        · -- n >= 187230215
          rcases Nat.lt_or_ge n 187410071 with hs4 | hs4
          · -- n < 187410071
            exact Brocard.berndt_galway_chunk_1042 n m (by omega) (by omega) h
          · -- n >= 187410071
            exact Brocard.berndt_galway_chunk_1043 n m (by omega) (by omega) h
  · -- n >= 187589928
    rcases Nat.lt_or_ge n 189748201 with hs1 | hs1
    · -- n < 189748201
      rcases Nat.lt_or_ge n 188669064 with hs2 | hs2
      · -- n < 188669064
        rcases Nat.lt_or_ge n 188129496 with hs3 | hs3
        · -- n < 188129496
          rcases Nat.lt_or_ge n 187949640 with hs4 | hs4
          · -- n < 187949640
            rcases Nat.lt_or_ge n 187769784 with hs5 | hs5
            · -- n < 187769784
              exact Brocard.berndt_galway_chunk_1044 n m (by omega) (by omega) h
            · -- n >= 187769784
              exact Brocard.berndt_galway_chunk_1045 n m (by omega) (by omega) h
          · -- n >= 187949640
            exact Brocard.berndt_galway_chunk_1046 n m (by omega) (by omega) h
        · -- n >= 188129496
          rcases Nat.lt_or_ge n 188489208 with hs4 | hs4
          · -- n < 188489208
            rcases Nat.lt_or_ge n 188309352 with hs5 | hs5
            · -- n < 188309352
              exact Brocard.berndt_galway_chunk_1047 n m (by omega) (by omega) h
            · -- n >= 188309352
              exact Brocard.berndt_galway_chunk_1048 n m (by omega) (by omega) h
          · -- n >= 188489208
            exact Brocard.berndt_galway_chunk_1049 n m (by omega) (by omega) h
      · -- n >= 188669064
        rcases Nat.lt_or_ge n 189208633 with hs3 | hs3
        · -- n < 189208633
          rcases Nat.lt_or_ge n 189028776 with hs4 | hs4
          · -- n < 189028776
            rcases Nat.lt_or_ge n 188848920 with hs5 | hs5
            · -- n < 188848920
              exact Brocard.berndt_galway_chunk_1050 n m (by omega) (by omega) h
            · -- n >= 188848920
              exact Brocard.berndt_galway_chunk_1051 n m (by omega) (by omega) h
          · -- n >= 189028776
            exact Brocard.berndt_galway_chunk_1052 n m (by omega) (by omega) h
        · -- n >= 189208633
          rcases Nat.lt_or_ge n 189568345 with hs4 | hs4
          · -- n < 189568345
            rcases Nat.lt_or_ge n 189388489 with hs5 | hs5
            · -- n < 189388489
              exact Brocard.berndt_galway_chunk_1053 n m (by omega) (by omega) h
            · -- n >= 189388489
              exact Brocard.berndt_galway_chunk_1054 n m (by omega) (by omega) h
          · -- n >= 189568345
            exact Brocard.berndt_galway_chunk_1055 n m (by omega) (by omega) h
    · -- n >= 189748201
      rcases Nat.lt_or_ge n 190827338 with hs2 | hs2
      · -- n < 190827338
        rcases Nat.lt_or_ge n 190287769 with hs3 | hs3
        · -- n < 190287769
          rcases Nat.lt_or_ge n 190107913 with hs4 | hs4
          · -- n < 190107913
            rcases Nat.lt_or_ge n 189928057 with hs5 | hs5
            · -- n < 189928057
              exact Brocard.berndt_galway_chunk_1056 n m (by omega) (by omega) h
            · -- n >= 189928057
              exact Brocard.berndt_galway_chunk_1057 n m (by omega) (by omega) h
          · -- n >= 190107913
            exact Brocard.berndt_galway_chunk_1058 n m (by omega) (by omega) h
        · -- n >= 190287769
          rcases Nat.lt_or_ge n 190647482 with hs4 | hs4
          · -- n < 190647482
            rcases Nat.lt_or_ge n 190467625 with hs5 | hs5
            · -- n < 190467625
              exact Brocard.berndt_galway_chunk_1059 n m (by omega) (by omega) h
            · -- n >= 190467625
              exact Brocard.berndt_galway_chunk_1060 n m (by omega) (by omega) h
          · -- n >= 190647482
            exact Brocard.berndt_galway_chunk_1061 n m (by omega) (by omega) h
      · -- n >= 190827338
        rcases Nat.lt_or_ge n 191366906 with hs3 | hs3
        · -- n < 191366906
          rcases Nat.lt_or_ge n 191187050 with hs4 | hs4
          · -- n < 191187050
            rcases Nat.lt_or_ge n 191007194 with hs5 | hs5
            · -- n < 191007194
              exact Brocard.berndt_galway_chunk_1062 n m (by omega) (by omega) h
            · -- n >= 191007194
              exact Brocard.berndt_galway_chunk_1063 n m (by omega) (by omega) h
          · -- n >= 191187050
            exact Brocard.berndt_galway_chunk_1064 n m (by omega) (by omega) h
        · -- n >= 191366906
          rcases Nat.lt_or_ge n 191546762 with hs4 | hs4
          · -- n < 191546762
            exact Brocard.berndt_galway_chunk_1065 n m (by omega) (by omega) h
          · -- n >= 191546762
            exact Brocard.berndt_galway_chunk_1066 n m (by omega) (by omega) h
