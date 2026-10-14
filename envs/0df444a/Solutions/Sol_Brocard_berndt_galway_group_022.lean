-- Prove2me | solution 1 for Brocard.berndt_galway_group_022
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:57:34.572534+00:00
-- url     : https://prove2.me/submissions/84b92e79-782c-4064-8261-8c4f6ef5ad35

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_0975
import Theorems.Thm_Brocard_berndt_galway_chunk_0976
import Theorems.Thm_Brocard_berndt_galway_chunk_0977
import Theorems.Thm_Brocard_berndt_galway_chunk_0978
import Theorems.Thm_Brocard_berndt_galway_chunk_0979
import Theorems.Thm_Brocard_berndt_galway_chunk_0980
import Theorems.Thm_Brocard_berndt_galway_chunk_0981
import Theorems.Thm_Brocard_berndt_galway_chunk_0982
import Theorems.Thm_Brocard_berndt_galway_chunk_0983
import Theorems.Thm_Brocard_berndt_galway_chunk_0984
import Theorems.Thm_Brocard_berndt_galway_chunk_0985
import Theorems.Thm_Brocard_berndt_galway_chunk_0986
import Theorems.Thm_Brocard_berndt_galway_chunk_0987
import Theorems.Thm_Brocard_berndt_galway_chunk_0988
import Theorems.Thm_Brocard_berndt_galway_chunk_0989
import Theorems.Thm_Brocard_berndt_galway_chunk_0990
import Theorems.Thm_Brocard_berndt_galway_chunk_0991
import Theorems.Thm_Brocard_berndt_galway_chunk_0992
import Theorems.Thm_Brocard_berndt_galway_chunk_0993
import Theorems.Thm_Brocard_berndt_galway_chunk_0994
import Theorems.Thm_Brocard_berndt_galway_chunk_0995
import Theorems.Thm_Brocard_berndt_galway_chunk_0996
import Theorems.Thm_Brocard_berndt_galway_chunk_0997
import Theorems.Thm_Brocard_berndt_galway_chunk_0998
import Theorems.Thm_Brocard_berndt_galway_chunk_0999
import Theorems.Thm_Brocard_berndt_galway_chunk_1000
import Theorems.Thm_Brocard_berndt_galway_chunk_1001
import Theorems.Thm_Brocard_berndt_galway_chunk_1002
import Theorems.Thm_Brocard_berndt_galway_chunk_1003
import Theorems.Thm_Brocard_berndt_galway_chunk_1004
import Theorems.Thm_Brocard_berndt_galway_chunk_1005
import Theorems.Thm_Brocard_berndt_galway_chunk_1006
import Theorems.Thm_Brocard_berndt_galway_chunk_1007
import Theorems.Thm_Brocard_berndt_galway_chunk_1008
import Theorems.Thm_Brocard_berndt_galway_chunk_1009
import Theorems.Thm_Brocard_berndt_galway_chunk_1010
import Theorems.Thm_Brocard_berndt_galway_chunk_1011
import Theorems.Thm_Brocard_berndt_galway_chunk_1012
import Theorems.Thm_Brocard_berndt_galway_chunk_1013
import Theorems.Thm_Brocard_berndt_galway_chunk_1014
import Theorems.Thm_Brocard_berndt_galway_chunk_1015
import Theorems.Thm_Brocard_berndt_galway_chunk_1016
import Theorems.Thm_Brocard_berndt_galway_chunk_1017
import Theorems.Thm_Brocard_berndt_galway_chunk_1018
import Theorems.Thm_Brocard_berndt_galway_chunk_1019
import Theorems.Thm_Brocard_berndt_galway_chunk_1020

theorem solution (n m : ℕ) (h1 : 175179856 ≤ n) (h2 : n < 183453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 179316546 with hs0 | hs0
  · -- n < 179316546
    rcases Nat.lt_or_ge n 177338129 with hs1 | hs1
    · -- n < 177338129
      rcases Nat.lt_or_ge n 176258992 with hs2 | hs2
      · -- n < 176258992
        rcases Nat.lt_or_ge n 175719424 with hs3 | hs3
        · -- n < 175719424
          rcases Nat.lt_or_ge n 175539568 with hs4 | hs4
          · -- n < 175539568
            rcases Nat.lt_or_ge n 175359712 with hs5 | hs5
            · -- n < 175359712
              exact Brocard.berndt_galway_chunk_0975 n m (by omega) (by omega) h
            · -- n >= 175359712
              exact Brocard.berndt_galway_chunk_0976 n m (by omega) (by omega) h
          · -- n >= 175539568
            exact Brocard.berndt_galway_chunk_0977 n m (by omega) (by omega) h
        · -- n >= 175719424
          rcases Nat.lt_or_ge n 176079136 with hs4 | hs4
          · -- n < 176079136
            rcases Nat.lt_or_ge n 175899280 with hs5 | hs5
            · -- n < 175899280
              exact Brocard.berndt_galway_chunk_0978 n m (by omega) (by omega) h
            · -- n >= 175899280
              exact Brocard.berndt_galway_chunk_0979 n m (by omega) (by omega) h
          · -- n >= 176079136
            exact Brocard.berndt_galway_chunk_0980 n m (by omega) (by omega) h
      · -- n >= 176258992
        rcases Nat.lt_or_ge n 176798561 with hs3 | hs3
        · -- n < 176798561
          rcases Nat.lt_or_ge n 176618705 with hs4 | hs4
          · -- n < 176618705
            rcases Nat.lt_or_ge n 176438848 with hs5 | hs5
            · -- n < 176438848
              exact Brocard.berndt_galway_chunk_0981 n m (by omega) (by omega) h
            · -- n >= 176438848
              exact Brocard.berndt_galway_chunk_0982 n m (by omega) (by omega) h
          · -- n >= 176618705
            exact Brocard.berndt_galway_chunk_0983 n m (by omega) (by omega) h
        · -- n >= 176798561
          rcases Nat.lt_or_ge n 177158273 with hs4 | hs4
          · -- n < 177158273
            rcases Nat.lt_or_ge n 176978417 with hs5 | hs5
            · -- n < 176978417
              exact Brocard.berndt_galway_chunk_0984 n m (by omega) (by omega) h
            · -- n >= 176978417
              exact Brocard.berndt_galway_chunk_0985 n m (by omega) (by omega) h
          · -- n >= 177158273
            exact Brocard.berndt_galway_chunk_0986 n m (by omega) (by omega) h
    · -- n >= 177338129
      rcases Nat.lt_or_ge n 178417266 with hs2 | hs2
      · -- n < 178417266
        rcases Nat.lt_or_ge n 177877697 with hs3 | hs3
        · -- n < 177877697
          rcases Nat.lt_or_ge n 177697841 with hs4 | hs4
          · -- n < 177697841
            rcases Nat.lt_or_ge n 177517985 with hs5 | hs5
            · -- n < 177517985
              exact Brocard.berndt_galway_chunk_0987 n m (by omega) (by omega) h
            · -- n >= 177517985
              exact Brocard.berndt_galway_chunk_0988 n m (by omega) (by omega) h
          · -- n >= 177697841
            exact Brocard.berndt_galway_chunk_0989 n m (by omega) (by omega) h
        · -- n >= 177877697
          rcases Nat.lt_or_ge n 178237410 with hs4 | hs4
          · -- n < 178237410
            rcases Nat.lt_or_ge n 178057553 with hs5 | hs5
            · -- n < 178057553
              exact Brocard.berndt_galway_chunk_0990 n m (by omega) (by omega) h
            · -- n >= 178057553
              exact Brocard.berndt_galway_chunk_0991 n m (by omega) (by omega) h
          · -- n >= 178237410
            exact Brocard.berndt_galway_chunk_0992 n m (by omega) (by omega) h
      · -- n >= 178417266
        rcases Nat.lt_or_ge n 178956834 with hs3 | hs3
        · -- n < 178956834
          rcases Nat.lt_or_ge n 178776978 with hs4 | hs4
          · -- n < 178776978
            rcases Nat.lt_or_ge n 178597122 with hs5 | hs5
            · -- n < 178597122
              exact Brocard.berndt_galway_chunk_0993 n m (by omega) (by omega) h
            · -- n >= 178597122
              exact Brocard.berndt_galway_chunk_0994 n m (by omega) (by omega) h
          · -- n >= 178776978
            exact Brocard.berndt_galway_chunk_0995 n m (by omega) (by omega) h
        · -- n >= 178956834
          rcases Nat.lt_or_ge n 179136690 with hs4 | hs4
          · -- n < 179136690
            exact Brocard.berndt_galway_chunk_0996 n m (by omega) (by omega) h
          · -- n >= 179136690
            exact Brocard.berndt_galway_chunk_0997 n m (by omega) (by omega) h
  · -- n >= 179316546
    rcases Nat.lt_or_ge n 181474820 with hs1 | hs1
    · -- n < 181474820
      rcases Nat.lt_or_ge n 180395683 with hs2 | hs2
      · -- n < 180395683
        rcases Nat.lt_or_ge n 179856115 with hs3 | hs3
        · -- n < 179856115
          rcases Nat.lt_or_ge n 179676258 with hs4 | hs4
          · -- n < 179676258
            rcases Nat.lt_or_ge n 179496402 with hs5 | hs5
            · -- n < 179496402
              exact Brocard.berndt_galway_chunk_0998 n m (by omega) (by omega) h
            · -- n >= 179496402
              exact Brocard.berndt_galway_chunk_0999 n m (by omega) (by omega) h
          · -- n >= 179676258
            exact Brocard.berndt_galway_chunk_1000 n m (by omega) (by omega) h
        · -- n >= 179856115
          rcases Nat.lt_or_ge n 180215827 with hs4 | hs4
          · -- n < 180215827
            rcases Nat.lt_or_ge n 180035971 with hs5 | hs5
            · -- n < 180035971
              exact Brocard.berndt_galway_chunk_1001 n m (by omega) (by omega) h
            · -- n >= 180035971
              exact Brocard.berndt_galway_chunk_1002 n m (by omega) (by omega) h
          · -- n >= 180215827
            exact Brocard.berndt_galway_chunk_1003 n m (by omega) (by omega) h
      · -- n >= 180395683
        rcases Nat.lt_or_ge n 180935251 with hs3 | hs3
        · -- n < 180935251
          rcases Nat.lt_or_ge n 180755395 with hs4 | hs4
          · -- n < 180755395
            rcases Nat.lt_or_ge n 180575539 with hs5 | hs5
            · -- n < 180575539
              exact Brocard.berndt_galway_chunk_1004 n m (by omega) (by omega) h
            · -- n >= 180575539
              exact Brocard.berndt_galway_chunk_1005 n m (by omega) (by omega) h
          · -- n >= 180755395
            exact Brocard.berndt_galway_chunk_1006 n m (by omega) (by omega) h
        · -- n >= 180935251
          rcases Nat.lt_or_ge n 181294964 with hs4 | hs4
          · -- n < 181294964
            rcases Nat.lt_or_ge n 181115107 with hs5 | hs5
            · -- n < 181115107
              exact Brocard.berndt_galway_chunk_1007 n m (by omega) (by omega) h
            · -- n >= 181115107
              exact Brocard.berndt_galway_chunk_1008 n m (by omega) (by omega) h
          · -- n >= 181294964
            exact Brocard.berndt_galway_chunk_1009 n m (by omega) (by omega) h
    · -- n >= 181474820
      rcases Nat.lt_or_ge n 182553956 with hs2 | hs2
      · -- n < 182553956
        rcases Nat.lt_or_ge n 182014388 with hs3 | hs3
        · -- n < 182014388
          rcases Nat.lt_or_ge n 181834532 with hs4 | hs4
          · -- n < 181834532
            rcases Nat.lt_or_ge n 181654676 with hs5 | hs5
            · -- n < 181654676
              exact Brocard.berndt_galway_chunk_1010 n m (by omega) (by omega) h
            · -- n >= 181654676
              exact Brocard.berndt_galway_chunk_1011 n m (by omega) (by omega) h
          · -- n >= 181834532
            exact Brocard.berndt_galway_chunk_1012 n m (by omega) (by omega) h
        · -- n >= 182014388
          rcases Nat.lt_or_ge n 182374100 with hs4 | hs4
          · -- n < 182374100
            rcases Nat.lt_or_ge n 182194244 with hs5 | hs5
            · -- n < 182194244
              exact Brocard.berndt_galway_chunk_1013 n m (by omega) (by omega) h
            · -- n >= 182194244
              exact Brocard.berndt_galway_chunk_1014 n m (by omega) (by omega) h
          · -- n >= 182374100
            exact Brocard.berndt_galway_chunk_1015 n m (by omega) (by omega) h
      · -- n >= 182553956
        rcases Nat.lt_or_ge n 183093525 with hs3 | hs3
        · -- n < 183093525
          rcases Nat.lt_or_ge n 182913669 with hs4 | hs4
          · -- n < 182913669
            rcases Nat.lt_or_ge n 182733812 with hs5 | hs5
            · -- n < 182733812
              exact Brocard.berndt_galway_chunk_1016 n m (by omega) (by omega) h
            · -- n >= 182733812
              exact Brocard.berndt_galway_chunk_1017 n m (by omega) (by omega) h
          · -- n >= 182913669
            exact Brocard.berndt_galway_chunk_1018 n m (by omega) (by omega) h
        · -- n >= 183093525
          rcases Nat.lt_or_ge n 183273381 with hs4 | hs4
          · -- n < 183273381
            exact Brocard.berndt_galway_chunk_1019 n m (by omega) (by omega) h
          · -- n >= 183273381
            exact Brocard.berndt_galway_chunk_1020 n m (by omega) (by omega) h
