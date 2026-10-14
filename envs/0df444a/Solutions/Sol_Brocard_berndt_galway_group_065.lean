-- Prove2me | solution 1 for Brocard.berndt_galway_group_065
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:32:43.33038+00:00
-- url     : https://prove2.me/submissions/165301d3-9ef6-4d4f-9813-d165eabaa48c

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_2969
import Theorems.Thm_Brocard_berndt_galway_chunk_2970
import Theorems.Thm_Brocard_berndt_galway_chunk_2971
import Theorems.Thm_Brocard_berndt_galway_chunk_2972
import Theorems.Thm_Brocard_berndt_galway_chunk_2973
import Theorems.Thm_Brocard_berndt_galway_chunk_2974
import Theorems.Thm_Brocard_berndt_galway_chunk_2975
import Theorems.Thm_Brocard_berndt_galway_chunk_2976
import Theorems.Thm_Brocard_berndt_galway_chunk_2977
import Theorems.Thm_Brocard_berndt_galway_chunk_2978
import Theorems.Thm_Brocard_berndt_galway_chunk_2979
import Theorems.Thm_Brocard_berndt_galway_chunk_2980
import Theorems.Thm_Brocard_berndt_galway_chunk_2981
import Theorems.Thm_Brocard_berndt_galway_chunk_2982
import Theorems.Thm_Brocard_berndt_galway_chunk_2983
import Theorems.Thm_Brocard_berndt_galway_chunk_2984
import Theorems.Thm_Brocard_berndt_galway_chunk_2985
import Theorems.Thm_Brocard_berndt_galway_chunk_2986
import Theorems.Thm_Brocard_berndt_galway_chunk_2987
import Theorems.Thm_Brocard_berndt_galway_chunk_2988
import Theorems.Thm_Brocard_berndt_galway_chunk_2989
import Theorems.Thm_Brocard_berndt_galway_chunk_2990
import Theorems.Thm_Brocard_berndt_galway_chunk_2991
import Theorems.Thm_Brocard_berndt_galway_chunk_2992
import Theorems.Thm_Brocard_berndt_galway_chunk_2993
import Theorems.Thm_Brocard_berndt_galway_chunk_2994
import Theorems.Thm_Brocard_berndt_galway_chunk_2995
import Theorems.Thm_Brocard_berndt_galway_chunk_2996
import Theorems.Thm_Brocard_berndt_galway_chunk_2997
import Theorems.Thm_Brocard_berndt_galway_chunk_2998
import Theorems.Thm_Brocard_berndt_galway_chunk_2999
import Theorems.Thm_Brocard_berndt_galway_chunk_3000
import Theorems.Thm_Brocard_berndt_galway_chunk_3001
import Theorems.Thm_Brocard_berndt_galway_chunk_3002
import Theorems.Thm_Brocard_berndt_galway_chunk_3003
import Theorems.Thm_Brocard_berndt_galway_chunk_3004
import Theorems.Thm_Brocard_berndt_galway_chunk_3005
import Theorems.Thm_Brocard_berndt_galway_chunk_3006
import Theorems.Thm_Brocard_berndt_galway_chunk_3007
import Theorems.Thm_Brocard_berndt_galway_chunk_3008
import Theorems.Thm_Brocard_berndt_galway_chunk_3009
import Theorems.Thm_Brocard_berndt_galway_chunk_3010
import Theorems.Thm_Brocard_berndt_galway_chunk_3011
import Theorems.Thm_Brocard_berndt_galway_chunk_3012
import Theorems.Thm_Brocard_berndt_galway_chunk_3013
import Theorems.Thm_Brocard_berndt_galway_chunk_3014

theorem solution (n m : ℕ) (h1 : 533812949 ≤ n) (h2 : n < 542086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 537949640 with hs0 | hs0
  · -- n < 537949640
    rcases Nat.lt_or_ge n 535971223 with hs1 | hs1
    · -- n < 535971223
      rcases Nat.lt_or_ge n 534892086 with hs2 | hs2
      · -- n < 534892086
        rcases Nat.lt_or_ge n 534352517 with hs3 | hs3
        · -- n < 534352517
          rcases Nat.lt_or_ge n 534172661 with hs4 | hs4
          · -- n < 534172661
            rcases Nat.lt_or_ge n 533992805 with hs5 | hs5
            · -- n < 533992805
              exact Brocard.berndt_galway_chunk_2969 n m (by omega) (by omega) h
            · -- n >= 533992805
              exact Brocard.berndt_galway_chunk_2970 n m (by omega) (by omega) h
          · -- n >= 534172661
            exact Brocard.berndt_galway_chunk_2971 n m (by omega) (by omega) h
        · -- n >= 534352517
          rcases Nat.lt_or_ge n 534712230 with hs4 | hs4
          · -- n < 534712230
            rcases Nat.lt_or_ge n 534532374 with hs5 | hs5
            · -- n < 534532374
              exact Brocard.berndt_galway_chunk_2972 n m (by omega) (by omega) h
            · -- n >= 534532374
              exact Brocard.berndt_galway_chunk_2973 n m (by omega) (by omega) h
          · -- n >= 534712230
            exact Brocard.berndt_galway_chunk_2974 n m (by omega) (by omega) h
      · -- n >= 534892086
        rcases Nat.lt_or_ge n 535431654 with hs3 | hs3
        · -- n < 535431654
          rcases Nat.lt_or_ge n 535251798 with hs4 | hs4
          · -- n < 535251798
            rcases Nat.lt_or_ge n 535071942 with hs5 | hs5
            · -- n < 535071942
              exact Brocard.berndt_galway_chunk_2975 n m (by omega) (by omega) h
            · -- n >= 535071942
              exact Brocard.berndt_galway_chunk_2976 n m (by omega) (by omega) h
          · -- n >= 535251798
            exact Brocard.berndt_galway_chunk_2977 n m (by omega) (by omega) h
        · -- n >= 535431654
          rcases Nat.lt_or_ge n 535791366 with hs4 | hs4
          · -- n < 535791366
            rcases Nat.lt_or_ge n 535611510 with hs5 | hs5
            · -- n < 535611510
              exact Brocard.berndt_galway_chunk_2978 n m (by omega) (by omega) h
            · -- n >= 535611510
              exact Brocard.berndt_galway_chunk_2979 n m (by omega) (by omega) h
          · -- n >= 535791366
            exact Brocard.berndt_galway_chunk_2980 n m (by omega) (by omega) h
    · -- n >= 535971223
      rcases Nat.lt_or_ge n 537050359 with hs2 | hs2
      · -- n < 537050359
        rcases Nat.lt_or_ge n 536510791 with hs3 | hs3
        · -- n < 536510791
          rcases Nat.lt_or_ge n 536330935 with hs4 | hs4
          · -- n < 536330935
            rcases Nat.lt_or_ge n 536151079 with hs5 | hs5
            · -- n < 536151079
              exact Brocard.berndt_galway_chunk_2981 n m (by omega) (by omega) h
            · -- n >= 536151079
              exact Brocard.berndt_galway_chunk_2982 n m (by omega) (by omega) h
          · -- n >= 536330935
            exact Brocard.berndt_galway_chunk_2983 n m (by omega) (by omega) h
        · -- n >= 536510791
          rcases Nat.lt_or_ge n 536870503 with hs4 | hs4
          · -- n < 536870503
            rcases Nat.lt_or_ge n 536690647 with hs5 | hs5
            · -- n < 536690647
              exact Brocard.berndt_galway_chunk_2984 n m (by omega) (by omega) h
            · -- n >= 536690647
              exact Brocard.berndt_galway_chunk_2985 n m (by omega) (by omega) h
          · -- n >= 536870503
            exact Brocard.berndt_galway_chunk_2986 n m (by omega) (by omega) h
      · -- n >= 537050359
        rcases Nat.lt_or_ge n 537589928 with hs3 | hs3
        · -- n < 537589928
          rcases Nat.lt_or_ge n 537410071 with hs4 | hs4
          · -- n < 537410071
            rcases Nat.lt_or_ge n 537230215 with hs5 | hs5
            · -- n < 537230215
              exact Brocard.berndt_galway_chunk_2987 n m (by omega) (by omega) h
            · -- n >= 537230215
              exact Brocard.berndt_galway_chunk_2988 n m (by omega) (by omega) h
          · -- n >= 537410071
            exact Brocard.berndt_galway_chunk_2989 n m (by omega) (by omega) h
        · -- n >= 537589928
          rcases Nat.lt_or_ge n 537769784 with hs4 | hs4
          · -- n < 537769784
            exact Brocard.berndt_galway_chunk_2990 n m (by omega) (by omega) h
          · -- n >= 537769784
            exact Brocard.berndt_galway_chunk_2991 n m (by omega) (by omega) h
  · -- n >= 537949640
    rcases Nat.lt_or_ge n 540107913 with hs1 | hs1
    · -- n < 540107913
      rcases Nat.lt_or_ge n 539028776 with hs2 | hs2
      · -- n < 539028776
        rcases Nat.lt_or_ge n 538489208 with hs3 | hs3
        · -- n < 538489208
          rcases Nat.lt_or_ge n 538309352 with hs4 | hs4
          · -- n < 538309352
            rcases Nat.lt_or_ge n 538129496 with hs5 | hs5
            · -- n < 538129496
              exact Brocard.berndt_galway_chunk_2992 n m (by omega) (by omega) h
            · -- n >= 538129496
              exact Brocard.berndt_galway_chunk_2993 n m (by omega) (by omega) h
          · -- n >= 538309352
            exact Brocard.berndt_galway_chunk_2994 n m (by omega) (by omega) h
        · -- n >= 538489208
          rcases Nat.lt_or_ge n 538848920 with hs4 | hs4
          · -- n < 538848920
            rcases Nat.lt_or_ge n 538669064 with hs5 | hs5
            · -- n < 538669064
              exact Brocard.berndt_galway_chunk_2995 n m (by omega) (by omega) h
            · -- n >= 538669064
              exact Brocard.berndt_galway_chunk_2996 n m (by omega) (by omega) h
          · -- n >= 538848920
            exact Brocard.berndt_galway_chunk_2997 n m (by omega) (by omega) h
      · -- n >= 539028776
        rcases Nat.lt_or_ge n 539568345 with hs3 | hs3
        · -- n < 539568345
          rcases Nat.lt_or_ge n 539388489 with hs4 | hs4
          · -- n < 539388489
            rcases Nat.lt_or_ge n 539208633 with hs5 | hs5
            · -- n < 539208633
              exact Brocard.berndt_galway_chunk_2998 n m (by omega) (by omega) h
            · -- n >= 539208633
              exact Brocard.berndt_galway_chunk_2999 n m (by omega) (by omega) h
          · -- n >= 539388489
            exact Brocard.berndt_galway_chunk_3000 n m (by omega) (by omega) h
        · -- n >= 539568345
          rcases Nat.lt_or_ge n 539928057 with hs4 | hs4
          · -- n < 539928057
            rcases Nat.lt_or_ge n 539748201 with hs5 | hs5
            · -- n < 539748201
              exact Brocard.berndt_galway_chunk_3001 n m (by omega) (by omega) h
            · -- n >= 539748201
              exact Brocard.berndt_galway_chunk_3002 n m (by omega) (by omega) h
          · -- n >= 539928057
            exact Brocard.berndt_galway_chunk_3003 n m (by omega) (by omega) h
    · -- n >= 540107913
      rcases Nat.lt_or_ge n 541187050 with hs2 | hs2
      · -- n < 541187050
        rcases Nat.lt_or_ge n 540647482 with hs3 | hs3
        · -- n < 540647482
          rcases Nat.lt_or_ge n 540467625 with hs4 | hs4
          · -- n < 540467625
            rcases Nat.lt_or_ge n 540287769 with hs5 | hs5
            · -- n < 540287769
              exact Brocard.berndt_galway_chunk_3004 n m (by omega) (by omega) h
            · -- n >= 540287769
              exact Brocard.berndt_galway_chunk_3005 n m (by omega) (by omega) h
          · -- n >= 540467625
            exact Brocard.berndt_galway_chunk_3006 n m (by omega) (by omega) h
        · -- n >= 540647482
          rcases Nat.lt_or_ge n 541007194 with hs4 | hs4
          · -- n < 541007194
            rcases Nat.lt_or_ge n 540827338 with hs5 | hs5
            · -- n < 540827338
              exact Brocard.berndt_galway_chunk_3007 n m (by omega) (by omega) h
            · -- n >= 540827338
              exact Brocard.berndt_galway_chunk_3008 n m (by omega) (by omega) h
          · -- n >= 541007194
            exact Brocard.berndt_galway_chunk_3009 n m (by omega) (by omega) h
      · -- n >= 541187050
        rcases Nat.lt_or_ge n 541726618 with hs3 | hs3
        · -- n < 541726618
          rcases Nat.lt_or_ge n 541546762 with hs4 | hs4
          · -- n < 541546762
            rcases Nat.lt_or_ge n 541366906 with hs5 | hs5
            · -- n < 541366906
              exact Brocard.berndt_galway_chunk_3010 n m (by omega) (by omega) h
            · -- n >= 541366906
              exact Brocard.berndt_galway_chunk_3011 n m (by omega) (by omega) h
          · -- n >= 541546762
            exact Brocard.berndt_galway_chunk_3012 n m (by omega) (by omega) h
        · -- n >= 541726618
          rcases Nat.lt_or_ge n 541906474 with hs4 | hs4
          · -- n < 541906474
            exact Brocard.berndt_galway_chunk_3013 n m (by omega) (by omega) h
          · -- n >= 541906474
            exact Brocard.berndt_galway_chunk_3014 n m (by omega) (by omega) h
