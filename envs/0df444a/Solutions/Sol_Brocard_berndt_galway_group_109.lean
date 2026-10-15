-- Prove2me | solution 1 for Brocard.berndt_galway_group_109
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:41:32.092172+00:00
-- url     : https://prove2.me/submissions/90e0c883-64c2-4fe7-b877-fa0abe64f971

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_5005
import Theorems.Thm_Brocard_berndt_galway_chunk_5006
import Theorems.Thm_Brocard_berndt_galway_chunk_5007
import Theorems.Thm_Brocard_berndt_galway_chunk_5008
import Theorems.Thm_Brocard_berndt_galway_chunk_5009
import Theorems.Thm_Brocard_berndt_galway_chunk_5010
import Theorems.Thm_Brocard_berndt_galway_chunk_5011
import Theorems.Thm_Brocard_berndt_galway_chunk_5012
import Theorems.Thm_Brocard_berndt_galway_chunk_5013
import Theorems.Thm_Brocard_berndt_galway_chunk_5014
import Theorems.Thm_Brocard_berndt_galway_chunk_5015
import Theorems.Thm_Brocard_berndt_galway_chunk_5016
import Theorems.Thm_Brocard_berndt_galway_chunk_5017
import Theorems.Thm_Brocard_berndt_galway_chunk_5018
import Theorems.Thm_Brocard_berndt_galway_chunk_5019
import Theorems.Thm_Brocard_berndt_galway_chunk_5020
import Theorems.Thm_Brocard_berndt_galway_chunk_5021
import Theorems.Thm_Brocard_berndt_galway_chunk_5022
import Theorems.Thm_Brocard_berndt_galway_chunk_5023
import Theorems.Thm_Brocard_berndt_galway_chunk_5024
import Theorems.Thm_Brocard_berndt_galway_chunk_5025
import Theorems.Thm_Brocard_berndt_galway_chunk_5026
import Theorems.Thm_Brocard_berndt_galway_chunk_5027
import Theorems.Thm_Brocard_berndt_galway_chunk_5028
import Theorems.Thm_Brocard_berndt_galway_chunk_5029
import Theorems.Thm_Brocard_berndt_galway_chunk_5030
import Theorems.Thm_Brocard_berndt_galway_chunk_5031
import Theorems.Thm_Brocard_berndt_galway_chunk_5032
import Theorems.Thm_Brocard_berndt_galway_chunk_5033
import Theorems.Thm_Brocard_berndt_galway_chunk_5034
import Theorems.Thm_Brocard_berndt_galway_chunk_5035
import Theorems.Thm_Brocard_berndt_galway_chunk_5036
import Theorems.Thm_Brocard_berndt_galway_chunk_5037
import Theorems.Thm_Brocard_berndt_galway_chunk_5038
import Theorems.Thm_Brocard_berndt_galway_chunk_5039
import Theorems.Thm_Brocard_berndt_galway_chunk_5040
import Theorems.Thm_Brocard_berndt_galway_chunk_5041
import Theorems.Thm_Brocard_berndt_galway_chunk_5042
import Theorems.Thm_Brocard_berndt_galway_chunk_5043
import Theorems.Thm_Brocard_berndt_galway_chunk_5044
import Theorems.Thm_Brocard_berndt_galway_chunk_5045
import Theorems.Thm_Brocard_berndt_galway_chunk_5046
import Theorems.Thm_Brocard_berndt_galway_chunk_5047
import Theorems.Thm_Brocard_berndt_galway_chunk_5048
import Theorems.Thm_Brocard_berndt_galway_chunk_5049
import Theorems.Thm_Brocard_berndt_galway_chunk_5050
import Theorems.Thm_Brocard_berndt_galway_chunk_5051

theorem solution (n m : ℕ) (h1 : 900000000 ≤ n) (h2 : n < 908453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 904316546 with hs0 | hs0
  · -- n < 904316546
    rcases Nat.lt_or_ge n 902158273 with hs1 | hs1
    · -- n < 902158273
      rcases Nat.lt_or_ge n 901079136 with hs2 | hs2
      · -- n < 901079136
        rcases Nat.lt_or_ge n 900539568 with hs3 | hs3
        · -- n < 900539568
          rcases Nat.lt_or_ge n 900359712 with hs4 | hs4
          · -- n < 900359712
            rcases Nat.lt_or_ge n 900179856 with hs5 | hs5
            · -- n < 900179856
              exact Brocard.berndt_galway_chunk_5005 n m (by omega) (by omega) h
            · -- n >= 900179856
              exact Brocard.berndt_galway_chunk_5006 n m (by omega) (by omega) h
          · -- n >= 900359712
            exact Brocard.berndt_galway_chunk_5007 n m (by omega) (by omega) h
        · -- n >= 900539568
          rcases Nat.lt_or_ge n 900899280 with hs4 | hs4
          · -- n < 900899280
            rcases Nat.lt_or_ge n 900719424 with hs5 | hs5
            · -- n < 900719424
              exact Brocard.berndt_galway_chunk_5008 n m (by omega) (by omega) h
            · -- n >= 900719424
              exact Brocard.berndt_galway_chunk_5009 n m (by omega) (by omega) h
          · -- n >= 900899280
            exact Brocard.berndt_galway_chunk_5010 n m (by omega) (by omega) h
      · -- n >= 901079136
        rcases Nat.lt_or_ge n 901618705 with hs3 | hs3
        · -- n < 901618705
          rcases Nat.lt_or_ge n 901438848 with hs4 | hs4
          · -- n < 901438848
            rcases Nat.lt_or_ge n 901258992 with hs5 | hs5
            · -- n < 901258992
              exact Brocard.berndt_galway_chunk_5011 n m (by omega) (by omega) h
            · -- n >= 901258992
              exact Brocard.berndt_galway_chunk_5012 n m (by omega) (by omega) h
          · -- n >= 901438848
            exact Brocard.berndt_galway_chunk_5013 n m (by omega) (by omega) h
        · -- n >= 901618705
          rcases Nat.lt_or_ge n 901978417 with hs4 | hs4
          · -- n < 901978417
            rcases Nat.lt_or_ge n 901798561 with hs5 | hs5
            · -- n < 901798561
              exact Brocard.berndt_galway_chunk_5014 n m (by omega) (by omega) h
            · -- n >= 901798561
              exact Brocard.berndt_galway_chunk_5015 n m (by omega) (by omega) h
          · -- n >= 901978417
            exact Brocard.berndt_galway_chunk_5016 n m (by omega) (by omega) h
    · -- n >= 902158273
      rcases Nat.lt_or_ge n 903237410 with hs2 | hs2
      · -- n < 903237410
        rcases Nat.lt_or_ge n 902697841 with hs3 | hs3
        · -- n < 902697841
          rcases Nat.lt_or_ge n 902517985 with hs4 | hs4
          · -- n < 902517985
            rcases Nat.lt_or_ge n 902338129 with hs5 | hs5
            · -- n < 902338129
              exact Brocard.berndt_galway_chunk_5017 n m (by omega) (by omega) h
            · -- n >= 902338129
              exact Brocard.berndt_galway_chunk_5018 n m (by omega) (by omega) h
          · -- n >= 902517985
            exact Brocard.berndt_galway_chunk_5019 n m (by omega) (by omega) h
        · -- n >= 902697841
          rcases Nat.lt_or_ge n 903057553 with hs4 | hs4
          · -- n < 903057553
            rcases Nat.lt_or_ge n 902877697 with hs5 | hs5
            · -- n < 902877697
              exact Brocard.berndt_galway_chunk_5020 n m (by omega) (by omega) h
            · -- n >= 902877697
              exact Brocard.berndt_galway_chunk_5021 n m (by omega) (by omega) h
          · -- n >= 903057553
            exact Brocard.berndt_galway_chunk_5022 n m (by omega) (by omega) h
      · -- n >= 903237410
        rcases Nat.lt_or_ge n 903776978 with hs3 | hs3
        · -- n < 903776978
          rcases Nat.lt_or_ge n 903597122 with hs4 | hs4
          · -- n < 903597122
            rcases Nat.lt_or_ge n 903417266 with hs5 | hs5
            · -- n < 903417266
              exact Brocard.berndt_galway_chunk_5023 n m (by omega) (by omega) h
            · -- n >= 903417266
              exact Brocard.berndt_galway_chunk_5024 n m (by omega) (by omega) h
          · -- n >= 903597122
            exact Brocard.berndt_galway_chunk_5025 n m (by omega) (by omega) h
        · -- n >= 903776978
          rcases Nat.lt_or_ge n 904136690 with hs4 | hs4
          · -- n < 904136690
            rcases Nat.lt_or_ge n 903956834 with hs5 | hs5
            · -- n < 903956834
              exact Brocard.berndt_galway_chunk_5026 n m (by omega) (by omega) h
            · -- n >= 903956834
              exact Brocard.berndt_galway_chunk_5027 n m (by omega) (by omega) h
          · -- n >= 904136690
            exact Brocard.berndt_galway_chunk_5028 n m (by omega) (by omega) h
  · -- n >= 904316546
    rcases Nat.lt_or_ge n 906474820 with hs1 | hs1
    · -- n < 906474820
      rcases Nat.lt_or_ge n 905395683 with hs2 | hs2
      · -- n < 905395683
        rcases Nat.lt_or_ge n 904856115 with hs3 | hs3
        · -- n < 904856115
          rcases Nat.lt_or_ge n 904676258 with hs4 | hs4
          · -- n < 904676258
            rcases Nat.lt_or_ge n 904496402 with hs5 | hs5
            · -- n < 904496402
              exact Brocard.berndt_galway_chunk_5029 n m (by omega) (by omega) h
            · -- n >= 904496402
              exact Brocard.berndt_galway_chunk_5030 n m (by omega) (by omega) h
          · -- n >= 904676258
            exact Brocard.berndt_galway_chunk_5031 n m (by omega) (by omega) h
        · -- n >= 904856115
          rcases Nat.lt_or_ge n 905215827 with hs4 | hs4
          · -- n < 905215827
            rcases Nat.lt_or_ge n 905035971 with hs5 | hs5
            · -- n < 905035971
              exact Brocard.berndt_galway_chunk_5032 n m (by omega) (by omega) h
            · -- n >= 905035971
              exact Brocard.berndt_galway_chunk_5033 n m (by omega) (by omega) h
          · -- n >= 905215827
            exact Brocard.berndt_galway_chunk_5034 n m (by omega) (by omega) h
      · -- n >= 905395683
        rcases Nat.lt_or_ge n 905935251 with hs3 | hs3
        · -- n < 905935251
          rcases Nat.lt_or_ge n 905755395 with hs4 | hs4
          · -- n < 905755395
            rcases Nat.lt_or_ge n 905575539 with hs5 | hs5
            · -- n < 905575539
              exact Brocard.berndt_galway_chunk_5035 n m (by omega) (by omega) h
            · -- n >= 905575539
              exact Brocard.berndt_galway_chunk_5036 n m (by omega) (by omega) h
          · -- n >= 905755395
            exact Brocard.berndt_galway_chunk_5037 n m (by omega) (by omega) h
        · -- n >= 905935251
          rcases Nat.lt_or_ge n 906294964 with hs4 | hs4
          · -- n < 906294964
            rcases Nat.lt_or_ge n 906115107 with hs5 | hs5
            · -- n < 906115107
              exact Brocard.berndt_galway_chunk_5038 n m (by omega) (by omega) h
            · -- n >= 906115107
              exact Brocard.berndt_galway_chunk_5039 n m (by omega) (by omega) h
          · -- n >= 906294964
            exact Brocard.berndt_galway_chunk_5040 n m (by omega) (by omega) h
    · -- n >= 906474820
      rcases Nat.lt_or_ge n 907553956 with hs2 | hs2
      · -- n < 907553956
        rcases Nat.lt_or_ge n 907014388 with hs3 | hs3
        · -- n < 907014388
          rcases Nat.lt_or_ge n 906834532 with hs4 | hs4
          · -- n < 906834532
            rcases Nat.lt_or_ge n 906654676 with hs5 | hs5
            · -- n < 906654676
              exact Brocard.berndt_galway_chunk_5041 n m (by omega) (by omega) h
            · -- n >= 906654676
              exact Brocard.berndt_galway_chunk_5042 n m (by omega) (by omega) h
          · -- n >= 906834532
            exact Brocard.berndt_galway_chunk_5043 n m (by omega) (by omega) h
        · -- n >= 907014388
          rcases Nat.lt_or_ge n 907374100 with hs4 | hs4
          · -- n < 907374100
            rcases Nat.lt_or_ge n 907194244 with hs5 | hs5
            · -- n < 907194244
              exact Brocard.berndt_galway_chunk_5044 n m (by omega) (by omega) h
            · -- n >= 907194244
              exact Brocard.berndt_galway_chunk_5045 n m (by omega) (by omega) h
          · -- n >= 907374100
            exact Brocard.berndt_galway_chunk_5046 n m (by omega) (by omega) h
      · -- n >= 907553956
        rcases Nat.lt_or_ge n 908093525 with hs3 | hs3
        · -- n < 908093525
          rcases Nat.lt_or_ge n 907913669 with hs4 | hs4
          · -- n < 907913669
            rcases Nat.lt_or_ge n 907733812 with hs5 | hs5
            · -- n < 907733812
              exact Brocard.berndt_galway_chunk_5047 n m (by omega) (by omega) h
            · -- n >= 907733812
              exact Brocard.berndt_galway_chunk_5048 n m (by omega) (by omega) h
          · -- n >= 907913669
            exact Brocard.berndt_galway_chunk_5049 n m (by omega) (by omega) h
        · -- n >= 908093525
          rcases Nat.lt_or_ge n 908273381 with hs4 | hs4
          · -- n < 908273381
            exact Brocard.berndt_galway_chunk_5050 n m (by omega) (by omega) h
          · -- n >= 908273381
            exact Brocard.berndt_galway_chunk_5051 n m (by omega) (by omega) h
