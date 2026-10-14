-- Prove2me | solution 1 for Brocard.berndt_galway_group_043
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:32:14.37569+00:00
-- url     : https://prove2.me/submissions/02a48e28-f35f-4853-b263-dc706d57aea6

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_1949
import Theorems.Thm_Brocard_berndt_galway_chunk_1950
import Theorems.Thm_Brocard_berndt_galway_chunk_1951
import Theorems.Thm_Brocard_berndt_galway_chunk_1952
import Theorems.Thm_Brocard_berndt_galway_chunk_1953
import Theorems.Thm_Brocard_berndt_galway_chunk_1954
import Theorems.Thm_Brocard_berndt_galway_chunk_1955
import Theorems.Thm_Brocard_berndt_galway_chunk_1956
import Theorems.Thm_Brocard_berndt_galway_chunk_1957
import Theorems.Thm_Brocard_berndt_galway_chunk_1958
import Theorems.Thm_Brocard_berndt_galway_chunk_1959
import Theorems.Thm_Brocard_berndt_galway_chunk_1960
import Theorems.Thm_Brocard_berndt_galway_chunk_1961
import Theorems.Thm_Brocard_berndt_galway_chunk_1962
import Theorems.Thm_Brocard_berndt_galway_chunk_1963
import Theorems.Thm_Brocard_berndt_galway_chunk_1964
import Theorems.Thm_Brocard_berndt_galway_chunk_1965
import Theorems.Thm_Brocard_berndt_galway_chunk_1966
import Theorems.Thm_Brocard_berndt_galway_chunk_1967
import Theorems.Thm_Brocard_berndt_galway_chunk_1968
import Theorems.Thm_Brocard_berndt_galway_chunk_1969
import Theorems.Thm_Brocard_berndt_galway_chunk_1970
import Theorems.Thm_Brocard_berndt_galway_chunk_1971
import Theorems.Thm_Brocard_berndt_galway_chunk_1972
import Theorems.Thm_Brocard_berndt_galway_chunk_1973
import Theorems.Thm_Brocard_berndt_galway_chunk_1974
import Theorems.Thm_Brocard_berndt_galway_chunk_1975
import Theorems.Thm_Brocard_berndt_galway_chunk_1976
import Theorems.Thm_Brocard_berndt_galway_chunk_1977
import Theorems.Thm_Brocard_berndt_galway_chunk_1978
import Theorems.Thm_Brocard_berndt_galway_chunk_1979
import Theorems.Thm_Brocard_berndt_galway_chunk_1980
import Theorems.Thm_Brocard_berndt_galway_chunk_1981
import Theorems.Thm_Brocard_berndt_galway_chunk_1982
import Theorems.Thm_Brocard_berndt_galway_chunk_1983
import Theorems.Thm_Brocard_berndt_galway_chunk_1984
import Theorems.Thm_Brocard_berndt_galway_chunk_1985
import Theorems.Thm_Brocard_berndt_galway_chunk_1986
import Theorems.Thm_Brocard_berndt_galway_chunk_1987
import Theorems.Thm_Brocard_berndt_galway_chunk_1988
import Theorems.Thm_Brocard_berndt_galway_chunk_1989
import Theorems.Thm_Brocard_berndt_galway_chunk_1990
import Theorems.Thm_Brocard_berndt_galway_chunk_1991
import Theorems.Thm_Brocard_berndt_galway_chunk_1992
import Theorems.Thm_Brocard_berndt_galway_chunk_1993
import Theorems.Thm_Brocard_berndt_galway_chunk_1994

theorem solution (n m : ℕ) (h1 : 350359712 ≤ n) (h2 : n < 358633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 354496402 with hs0 | hs0
  · -- n < 354496402
    rcases Nat.lt_or_ge n 352517985 with hs1 | hs1
    · -- n < 352517985
      rcases Nat.lt_or_ge n 351438848 with hs2 | hs2
      · -- n < 351438848
        rcases Nat.lt_or_ge n 350899280 with hs3 | hs3
        · -- n < 350899280
          rcases Nat.lt_or_ge n 350719424 with hs4 | hs4
          · -- n < 350719424
            rcases Nat.lt_or_ge n 350539568 with hs5 | hs5
            · -- n < 350539568
              exact Brocard.berndt_galway_chunk_1949 n m (by omega) (by omega) h
            · -- n >= 350539568
              exact Brocard.berndt_galway_chunk_1950 n m (by omega) (by omega) h
          · -- n >= 350719424
            exact Brocard.berndt_galway_chunk_1951 n m (by omega) (by omega) h
        · -- n >= 350899280
          rcases Nat.lt_or_ge n 351258992 with hs4 | hs4
          · -- n < 351258992
            rcases Nat.lt_or_ge n 351079136 with hs5 | hs5
            · -- n < 351079136
              exact Brocard.berndt_galway_chunk_1952 n m (by omega) (by omega) h
            · -- n >= 351079136
              exact Brocard.berndt_galway_chunk_1953 n m (by omega) (by omega) h
          · -- n >= 351258992
            exact Brocard.berndt_galway_chunk_1954 n m (by omega) (by omega) h
      · -- n >= 351438848
        rcases Nat.lt_or_ge n 351978417 with hs3 | hs3
        · -- n < 351978417
          rcases Nat.lt_or_ge n 351798561 with hs4 | hs4
          · -- n < 351798561
            rcases Nat.lt_or_ge n 351618705 with hs5 | hs5
            · -- n < 351618705
              exact Brocard.berndt_galway_chunk_1955 n m (by omega) (by omega) h
            · -- n >= 351618705
              exact Brocard.berndt_galway_chunk_1956 n m (by omega) (by omega) h
          · -- n >= 351798561
            exact Brocard.berndt_galway_chunk_1957 n m (by omega) (by omega) h
        · -- n >= 351978417
          rcases Nat.lt_or_ge n 352338129 with hs4 | hs4
          · -- n < 352338129
            rcases Nat.lt_or_ge n 352158273 with hs5 | hs5
            · -- n < 352158273
              exact Brocard.berndt_galway_chunk_1958 n m (by omega) (by omega) h
            · -- n >= 352158273
              exact Brocard.berndt_galway_chunk_1959 n m (by omega) (by omega) h
          · -- n >= 352338129
            exact Brocard.berndt_galway_chunk_1960 n m (by omega) (by omega) h
    · -- n >= 352517985
      rcases Nat.lt_or_ge n 353597122 with hs2 | hs2
      · -- n < 353597122
        rcases Nat.lt_or_ge n 353057553 with hs3 | hs3
        · -- n < 353057553
          rcases Nat.lt_or_ge n 352877697 with hs4 | hs4
          · -- n < 352877697
            rcases Nat.lt_or_ge n 352697841 with hs5 | hs5
            · -- n < 352697841
              exact Brocard.berndt_galway_chunk_1961 n m (by omega) (by omega) h
            · -- n >= 352697841
              exact Brocard.berndt_galway_chunk_1962 n m (by omega) (by omega) h
          · -- n >= 352877697
            exact Brocard.berndt_galway_chunk_1963 n m (by omega) (by omega) h
        · -- n >= 353057553
          rcases Nat.lt_or_ge n 353417266 with hs4 | hs4
          · -- n < 353417266
            rcases Nat.lt_or_ge n 353237410 with hs5 | hs5
            · -- n < 353237410
              exact Brocard.berndt_galway_chunk_1964 n m (by omega) (by omega) h
            · -- n >= 353237410
              exact Brocard.berndt_galway_chunk_1965 n m (by omega) (by omega) h
          · -- n >= 353417266
            exact Brocard.berndt_galway_chunk_1966 n m (by omega) (by omega) h
      · -- n >= 353597122
        rcases Nat.lt_or_ge n 354136690 with hs3 | hs3
        · -- n < 354136690
          rcases Nat.lt_or_ge n 353956834 with hs4 | hs4
          · -- n < 353956834
            rcases Nat.lt_or_ge n 353776978 with hs5 | hs5
            · -- n < 353776978
              exact Brocard.berndt_galway_chunk_1967 n m (by omega) (by omega) h
            · -- n >= 353776978
              exact Brocard.berndt_galway_chunk_1968 n m (by omega) (by omega) h
          · -- n >= 353956834
            exact Brocard.berndt_galway_chunk_1969 n m (by omega) (by omega) h
        · -- n >= 354136690
          rcases Nat.lt_or_ge n 354316546 with hs4 | hs4
          · -- n < 354316546
            exact Brocard.berndt_galway_chunk_1970 n m (by omega) (by omega) h
          · -- n >= 354316546
            exact Brocard.berndt_galway_chunk_1971 n m (by omega) (by omega) h
  · -- n >= 354496402
    rcases Nat.lt_or_ge n 356654676 with hs1 | hs1
    · -- n < 356654676
      rcases Nat.lt_or_ge n 355575539 with hs2 | hs2
      · -- n < 355575539
        rcases Nat.lt_or_ge n 355035971 with hs3 | hs3
        · -- n < 355035971
          rcases Nat.lt_or_ge n 354856115 with hs4 | hs4
          · -- n < 354856115
            rcases Nat.lt_or_ge n 354676258 with hs5 | hs5
            · -- n < 354676258
              exact Brocard.berndt_galway_chunk_1972 n m (by omega) (by omega) h
            · -- n >= 354676258
              exact Brocard.berndt_galway_chunk_1973 n m (by omega) (by omega) h
          · -- n >= 354856115
            exact Brocard.berndt_galway_chunk_1974 n m (by omega) (by omega) h
        · -- n >= 355035971
          rcases Nat.lt_or_ge n 355395683 with hs4 | hs4
          · -- n < 355395683
            rcases Nat.lt_or_ge n 355215827 with hs5 | hs5
            · -- n < 355215827
              exact Brocard.berndt_galway_chunk_1975 n m (by omega) (by omega) h
            · -- n >= 355215827
              exact Brocard.berndt_galway_chunk_1976 n m (by omega) (by omega) h
          · -- n >= 355395683
            exact Brocard.berndt_galway_chunk_1977 n m (by omega) (by omega) h
      · -- n >= 355575539
        rcases Nat.lt_or_ge n 356115107 with hs3 | hs3
        · -- n < 356115107
          rcases Nat.lt_or_ge n 355935251 with hs4 | hs4
          · -- n < 355935251
            rcases Nat.lt_or_ge n 355755395 with hs5 | hs5
            · -- n < 355755395
              exact Brocard.berndt_galway_chunk_1978 n m (by omega) (by omega) h
            · -- n >= 355755395
              exact Brocard.berndt_galway_chunk_1979 n m (by omega) (by omega) h
          · -- n >= 355935251
            exact Brocard.berndt_galway_chunk_1980 n m (by omega) (by omega) h
        · -- n >= 356115107
          rcases Nat.lt_or_ge n 356474820 with hs4 | hs4
          · -- n < 356474820
            rcases Nat.lt_or_ge n 356294964 with hs5 | hs5
            · -- n < 356294964
              exact Brocard.berndt_galway_chunk_1981 n m (by omega) (by omega) h
            · -- n >= 356294964
              exact Brocard.berndt_galway_chunk_1982 n m (by omega) (by omega) h
          · -- n >= 356474820
            exact Brocard.berndt_galway_chunk_1983 n m (by omega) (by omega) h
    · -- n >= 356654676
      rcases Nat.lt_or_ge n 357733812 with hs2 | hs2
      · -- n < 357733812
        rcases Nat.lt_or_ge n 357194244 with hs3 | hs3
        · -- n < 357194244
          rcases Nat.lt_or_ge n 357014388 with hs4 | hs4
          · -- n < 357014388
            rcases Nat.lt_or_ge n 356834532 with hs5 | hs5
            · -- n < 356834532
              exact Brocard.berndt_galway_chunk_1984 n m (by omega) (by omega) h
            · -- n >= 356834532
              exact Brocard.berndt_galway_chunk_1985 n m (by omega) (by omega) h
          · -- n >= 357014388
            exact Brocard.berndt_galway_chunk_1986 n m (by omega) (by omega) h
        · -- n >= 357194244
          rcases Nat.lt_or_ge n 357553956 with hs4 | hs4
          · -- n < 357553956
            rcases Nat.lt_or_ge n 357374100 with hs5 | hs5
            · -- n < 357374100
              exact Brocard.berndt_galway_chunk_1987 n m (by omega) (by omega) h
            · -- n >= 357374100
              exact Brocard.berndt_galway_chunk_1988 n m (by omega) (by omega) h
          · -- n >= 357553956
            exact Brocard.berndt_galway_chunk_1989 n m (by omega) (by omega) h
      · -- n >= 357733812
        rcases Nat.lt_or_ge n 358273381 with hs3 | hs3
        · -- n < 358273381
          rcases Nat.lt_or_ge n 358093525 with hs4 | hs4
          · -- n < 358093525
            rcases Nat.lt_or_ge n 357913669 with hs5 | hs5
            · -- n < 357913669
              exact Brocard.berndt_galway_chunk_1990 n m (by omega) (by omega) h
            · -- n >= 357913669
              exact Brocard.berndt_galway_chunk_1991 n m (by omega) (by omega) h
          · -- n >= 358093525
            exact Brocard.berndt_galway_chunk_1992 n m (by omega) (by omega) h
        · -- n >= 358273381
          rcases Nat.lt_or_ge n 358453237 with hs4 | hs4
          · -- n < 358453237
            exact Brocard.berndt_galway_chunk_1993 n m (by omega) (by omega) h
          · -- n >= 358453237
            exact Brocard.berndt_galway_chunk_1994 n m (by omega) (by omega) h
