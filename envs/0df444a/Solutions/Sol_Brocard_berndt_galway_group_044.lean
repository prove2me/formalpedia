-- Prove2me | solution 1 for Brocard.berndt_galway_group_044
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:35:50.055007+00:00
-- url     : https://prove2.me/submissions/88019981-122c-4374-b2ca-34b97a8758b6

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_1995
import Theorems.Thm_Brocard_berndt_galway_chunk_1996
import Theorems.Thm_Brocard_berndt_galway_chunk_1997
import Theorems.Thm_Brocard_berndt_galway_chunk_1998
import Theorems.Thm_Brocard_berndt_galway_chunk_1999
import Theorems.Thm_Brocard_berndt_galway_chunk_2000
import Theorems.Thm_Brocard_berndt_galway_chunk_2001
import Theorems.Thm_Brocard_berndt_galway_chunk_2002
import Theorems.Thm_Brocard_berndt_galway_chunk_2003
import Theorems.Thm_Brocard_berndt_galway_chunk_2004
import Theorems.Thm_Brocard_berndt_galway_chunk_2005
import Theorems.Thm_Brocard_berndt_galway_chunk_2006
import Theorems.Thm_Brocard_berndt_galway_chunk_2007
import Theorems.Thm_Brocard_berndt_galway_chunk_2008
import Theorems.Thm_Brocard_berndt_galway_chunk_2009
import Theorems.Thm_Brocard_berndt_galway_chunk_2010
import Theorems.Thm_Brocard_berndt_galway_chunk_2011
import Theorems.Thm_Brocard_berndt_galway_chunk_2012
import Theorems.Thm_Brocard_berndt_galway_chunk_2013
import Theorems.Thm_Brocard_berndt_galway_chunk_2014
import Theorems.Thm_Brocard_berndt_galway_chunk_2015
import Theorems.Thm_Brocard_berndt_galway_chunk_2016
import Theorems.Thm_Brocard_berndt_galway_chunk_2017
import Theorems.Thm_Brocard_berndt_galway_chunk_2018
import Theorems.Thm_Brocard_berndt_galway_chunk_2019
import Theorems.Thm_Brocard_berndt_galway_chunk_2020
import Theorems.Thm_Brocard_berndt_galway_chunk_2021
import Theorems.Thm_Brocard_berndt_galway_chunk_2022
import Theorems.Thm_Brocard_berndt_galway_chunk_2023
import Theorems.Thm_Brocard_berndt_galway_chunk_2024
import Theorems.Thm_Brocard_berndt_galway_chunk_2025
import Theorems.Thm_Brocard_berndt_galway_chunk_2026
import Theorems.Thm_Brocard_berndt_galway_chunk_2027
import Theorems.Thm_Brocard_berndt_galway_chunk_2028
import Theorems.Thm_Brocard_berndt_galway_chunk_2029
import Theorems.Thm_Brocard_berndt_galway_chunk_2030
import Theorems.Thm_Brocard_berndt_galway_chunk_2031
import Theorems.Thm_Brocard_berndt_galway_chunk_2032
import Theorems.Thm_Brocard_berndt_galway_chunk_2033
import Theorems.Thm_Brocard_berndt_galway_chunk_2034
import Theorems.Thm_Brocard_berndt_galway_chunk_2035
import Theorems.Thm_Brocard_berndt_galway_chunk_2036
import Theorems.Thm_Brocard_berndt_galway_chunk_2037
import Theorems.Thm_Brocard_berndt_galway_chunk_2038
import Theorems.Thm_Brocard_berndt_galway_chunk_2039
import Theorems.Thm_Brocard_berndt_galway_chunk_2040

theorem solution (n m : ℕ) (h1 : 358633093 ≤ n) (h2 : n < 366906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 362769784 with hs0 | hs0
  · -- n < 362769784
    rcases Nat.lt_or_ge n 360791366 with hs1 | hs1
    · -- n < 360791366
      rcases Nat.lt_or_ge n 359712230 with hs2 | hs2
      · -- n < 359712230
        rcases Nat.lt_or_ge n 359172661 with hs3 | hs3
        · -- n < 359172661
          rcases Nat.lt_or_ge n 358992805 with hs4 | hs4
          · -- n < 358992805
            rcases Nat.lt_or_ge n 358812949 with hs5 | hs5
            · -- n < 358812949
              exact Brocard.berndt_galway_chunk_1995 n m (by omega) (by omega) h
            · -- n >= 358812949
              exact Brocard.berndt_galway_chunk_1996 n m (by omega) (by omega) h
          · -- n >= 358992805
            exact Brocard.berndt_galway_chunk_1997 n m (by omega) (by omega) h
        · -- n >= 359172661
          rcases Nat.lt_or_ge n 359532374 with hs4 | hs4
          · -- n < 359532374
            rcases Nat.lt_or_ge n 359352517 with hs5 | hs5
            · -- n < 359352517
              exact Brocard.berndt_galway_chunk_1998 n m (by omega) (by omega) h
            · -- n >= 359352517
              exact Brocard.berndt_galway_chunk_1999 n m (by omega) (by omega) h
          · -- n >= 359532374
            exact Brocard.berndt_galway_chunk_2000 n m (by omega) (by omega) h
      · -- n >= 359712230
        rcases Nat.lt_or_ge n 360251798 with hs3 | hs3
        · -- n < 360251798
          rcases Nat.lt_or_ge n 360071942 with hs4 | hs4
          · -- n < 360071942
            rcases Nat.lt_or_ge n 359892086 with hs5 | hs5
            · -- n < 359892086
              exact Brocard.berndt_galway_chunk_2001 n m (by omega) (by omega) h
            · -- n >= 359892086
              exact Brocard.berndt_galway_chunk_2002 n m (by omega) (by omega) h
          · -- n >= 360071942
            exact Brocard.berndt_galway_chunk_2003 n m (by omega) (by omega) h
        · -- n >= 360251798
          rcases Nat.lt_or_ge n 360611510 with hs4 | hs4
          · -- n < 360611510
            rcases Nat.lt_or_ge n 360431654 with hs5 | hs5
            · -- n < 360431654
              exact Brocard.berndt_galway_chunk_2004 n m (by omega) (by omega) h
            · -- n >= 360431654
              exact Brocard.berndt_galway_chunk_2005 n m (by omega) (by omega) h
          · -- n >= 360611510
            exact Brocard.berndt_galway_chunk_2006 n m (by omega) (by omega) h
    · -- n >= 360791366
      rcases Nat.lt_or_ge n 361870503 with hs2 | hs2
      · -- n < 361870503
        rcases Nat.lt_or_ge n 361330935 with hs3 | hs3
        · -- n < 361330935
          rcases Nat.lt_or_ge n 361151079 with hs4 | hs4
          · -- n < 361151079
            rcases Nat.lt_or_ge n 360971223 with hs5 | hs5
            · -- n < 360971223
              exact Brocard.berndt_galway_chunk_2007 n m (by omega) (by omega) h
            · -- n >= 360971223
              exact Brocard.berndt_galway_chunk_2008 n m (by omega) (by omega) h
          · -- n >= 361151079
            exact Brocard.berndt_galway_chunk_2009 n m (by omega) (by omega) h
        · -- n >= 361330935
          rcases Nat.lt_or_ge n 361690647 with hs4 | hs4
          · -- n < 361690647
            rcases Nat.lt_or_ge n 361510791 with hs5 | hs5
            · -- n < 361510791
              exact Brocard.berndt_galway_chunk_2010 n m (by omega) (by omega) h
            · -- n >= 361510791
              exact Brocard.berndt_galway_chunk_2011 n m (by omega) (by omega) h
          · -- n >= 361690647
            exact Brocard.berndt_galway_chunk_2012 n m (by omega) (by omega) h
      · -- n >= 361870503
        rcases Nat.lt_or_ge n 362410071 with hs3 | hs3
        · -- n < 362410071
          rcases Nat.lt_or_ge n 362230215 with hs4 | hs4
          · -- n < 362230215
            rcases Nat.lt_or_ge n 362050359 with hs5 | hs5
            · -- n < 362050359
              exact Brocard.berndt_galway_chunk_2013 n m (by omega) (by omega) h
            · -- n >= 362050359
              exact Brocard.berndt_galway_chunk_2014 n m (by omega) (by omega) h
          · -- n >= 362230215
            exact Brocard.berndt_galway_chunk_2015 n m (by omega) (by omega) h
        · -- n >= 362410071
          rcases Nat.lt_or_ge n 362589928 with hs4 | hs4
          · -- n < 362589928
            exact Brocard.berndt_galway_chunk_2016 n m (by omega) (by omega) h
          · -- n >= 362589928
            exact Brocard.berndt_galway_chunk_2017 n m (by omega) (by omega) h
  · -- n >= 362769784
    rcases Nat.lt_or_ge n 364928057 with hs1 | hs1
    · -- n < 364928057
      rcases Nat.lt_or_ge n 363848920 with hs2 | hs2
      · -- n < 363848920
        rcases Nat.lt_or_ge n 363309352 with hs3 | hs3
        · -- n < 363309352
          rcases Nat.lt_or_ge n 363129496 with hs4 | hs4
          · -- n < 363129496
            rcases Nat.lt_or_ge n 362949640 with hs5 | hs5
            · -- n < 362949640
              exact Brocard.berndt_galway_chunk_2018 n m (by omega) (by omega) h
            · -- n >= 362949640
              exact Brocard.berndt_galway_chunk_2019 n m (by omega) (by omega) h
          · -- n >= 363129496
            exact Brocard.berndt_galway_chunk_2020 n m (by omega) (by omega) h
        · -- n >= 363309352
          rcases Nat.lt_or_ge n 363669064 with hs4 | hs4
          · -- n < 363669064
            rcases Nat.lt_or_ge n 363489208 with hs5 | hs5
            · -- n < 363489208
              exact Brocard.berndt_galway_chunk_2021 n m (by omega) (by omega) h
            · -- n >= 363489208
              exact Brocard.berndt_galway_chunk_2022 n m (by omega) (by omega) h
          · -- n >= 363669064
            exact Brocard.berndt_galway_chunk_2023 n m (by omega) (by omega) h
      · -- n >= 363848920
        rcases Nat.lt_or_ge n 364388489 with hs3 | hs3
        · -- n < 364388489
          rcases Nat.lt_or_ge n 364208633 with hs4 | hs4
          · -- n < 364208633
            rcases Nat.lt_or_ge n 364028776 with hs5 | hs5
            · -- n < 364028776
              exact Brocard.berndt_galway_chunk_2024 n m (by omega) (by omega) h
            · -- n >= 364028776
              exact Brocard.berndt_galway_chunk_2025 n m (by omega) (by omega) h
          · -- n >= 364208633
            exact Brocard.berndt_galway_chunk_2026 n m (by omega) (by omega) h
        · -- n >= 364388489
          rcases Nat.lt_or_ge n 364748201 with hs4 | hs4
          · -- n < 364748201
            rcases Nat.lt_or_ge n 364568345 with hs5 | hs5
            · -- n < 364568345
              exact Brocard.berndt_galway_chunk_2027 n m (by omega) (by omega) h
            · -- n >= 364568345
              exact Brocard.berndt_galway_chunk_2028 n m (by omega) (by omega) h
          · -- n >= 364748201
            exact Brocard.berndt_galway_chunk_2029 n m (by omega) (by omega) h
    · -- n >= 364928057
      rcases Nat.lt_or_ge n 366007194 with hs2 | hs2
      · -- n < 366007194
        rcases Nat.lt_or_ge n 365467625 with hs3 | hs3
        · -- n < 365467625
          rcases Nat.lt_or_ge n 365287769 with hs4 | hs4
          · -- n < 365287769
            rcases Nat.lt_or_ge n 365107913 with hs5 | hs5
            · -- n < 365107913
              exact Brocard.berndt_galway_chunk_2030 n m (by omega) (by omega) h
            · -- n >= 365107913
              exact Brocard.berndt_galway_chunk_2031 n m (by omega) (by omega) h
          · -- n >= 365287769
            exact Brocard.berndt_galway_chunk_2032 n m (by omega) (by omega) h
        · -- n >= 365467625
          rcases Nat.lt_or_ge n 365827338 with hs4 | hs4
          · -- n < 365827338
            rcases Nat.lt_or_ge n 365647482 with hs5 | hs5
            · -- n < 365647482
              exact Brocard.berndt_galway_chunk_2033 n m (by omega) (by omega) h
            · -- n >= 365647482
              exact Brocard.berndt_galway_chunk_2034 n m (by omega) (by omega) h
          · -- n >= 365827338
            exact Brocard.berndt_galway_chunk_2035 n m (by omega) (by omega) h
      · -- n >= 366007194
        rcases Nat.lt_or_ge n 366546762 with hs3 | hs3
        · -- n < 366546762
          rcases Nat.lt_or_ge n 366366906 with hs4 | hs4
          · -- n < 366366906
            rcases Nat.lt_or_ge n 366187050 with hs5 | hs5
            · -- n < 366187050
              exact Brocard.berndt_galway_chunk_2036 n m (by omega) (by omega) h
            · -- n >= 366187050
              exact Brocard.berndt_galway_chunk_2037 n m (by omega) (by omega) h
          · -- n >= 366366906
            exact Brocard.berndt_galway_chunk_2038 n m (by omega) (by omega) h
        · -- n >= 366546762
          rcases Nat.lt_or_ge n 366726618 with hs4 | hs4
          · -- n < 366726618
            exact Brocard.berndt_galway_chunk_2039 n m (by omega) (by omega) h
          · -- n >= 366726618
            exact Brocard.berndt_galway_chunk_2040 n m (by omega) (by omega) h
