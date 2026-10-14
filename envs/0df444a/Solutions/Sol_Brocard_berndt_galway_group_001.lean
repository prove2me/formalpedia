-- Prove2me | solution 1 for Brocard.berndt_galway_group_001
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:39:53.604013+00:00
-- url     : https://prove2.me/submissions/61303070-cf43-427c-a9b5-292469d54774

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_0001
import Theorems.Thm_Brocard_berndt_galway_chunk_0002
import Theorems.Thm_Brocard_berndt_galway_chunk_0003
import Theorems.Thm_Brocard_berndt_galway_chunk_0004
import Theorems.Thm_Brocard_berndt_galway_chunk_0005
import Theorems.Thm_Brocard_berndt_galway_chunk_0006
import Theorems.Thm_Brocard_berndt_galway_chunk_0007
import Theorems.Thm_Brocard_berndt_galway_chunk_0008
import Theorems.Thm_Brocard_berndt_galway_chunk_0009
import Theorems.Thm_Brocard_berndt_galway_chunk_0010
import Theorems.Thm_Brocard_berndt_galway_chunk_0011
import Theorems.Thm_Brocard_berndt_galway_chunk_0012
import Theorems.Thm_Brocard_berndt_galway_chunk_0013
import Theorems.Thm_Brocard_berndt_galway_chunk_0014
import Theorems.Thm_Brocard_berndt_galway_chunk_0015
import Theorems.Thm_Brocard_berndt_galway_chunk_0016
import Theorems.Thm_Brocard_berndt_galway_chunk_0017
import Theorems.Thm_Brocard_berndt_galway_chunk_0018
import Theorems.Thm_Brocard_berndt_galway_chunk_0019
import Theorems.Thm_Brocard_berndt_galway_chunk_0020
import Theorems.Thm_Brocard_berndt_galway_chunk_0021
import Theorems.Thm_Brocard_berndt_galway_chunk_0022
import Theorems.Thm_Brocard_berndt_galway_chunk_0023
import Theorems.Thm_Brocard_berndt_galway_chunk_0024
import Theorems.Thm_Brocard_berndt_galway_chunk_0025
import Theorems.Thm_Brocard_berndt_galway_chunk_0026
import Theorems.Thm_Brocard_berndt_galway_chunk_0027
import Theorems.Thm_Brocard_berndt_galway_chunk_0028
import Theorems.Thm_Brocard_berndt_galway_chunk_0029
import Theorems.Thm_Brocard_berndt_galway_chunk_0030
import Theorems.Thm_Brocard_berndt_galway_chunk_0031
import Theorems.Thm_Brocard_berndt_galway_chunk_0032
import Theorems.Thm_Brocard_berndt_galway_chunk_0033
import Theorems.Thm_Brocard_berndt_galway_chunk_0034
import Theorems.Thm_Brocard_berndt_galway_chunk_0035
import Theorems.Thm_Brocard_berndt_galway_chunk_0036
import Theorems.Thm_Brocard_berndt_galway_chunk_0037
import Theorems.Thm_Brocard_berndt_galway_chunk_0038
import Theorems.Thm_Brocard_berndt_galway_chunk_0039
import Theorems.Thm_Brocard_berndt_galway_chunk_0040
import Theorems.Thm_Brocard_berndt_galway_chunk_0041
import Theorems.Thm_Brocard_berndt_galway_chunk_0042
import Theorems.Thm_Brocard_berndt_galway_chunk_0043
import Theorems.Thm_Brocard_berndt_galway_chunk_0044
import Theorems.Thm_Brocard_berndt_galway_chunk_0045
import Theorems.Thm_Brocard_berndt_galway_chunk_0046
import Theorems.Thm_Brocard_berndt_galway_chunk_0047

theorem solution (n m : ℕ) (h1 : 8 ≤ n) (h2 : n < 8453244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 4316554 with hs0 | hs0
  · -- n < 4316554
    rcases Nat.lt_or_ge n 2158281 with hs1 | hs1
    · -- n < 2158281
      rcases Nat.lt_or_ge n 1079144 with hs2 | hs2
      · -- n < 1079144
        rcases Nat.lt_or_ge n 539576 with hs3 | hs3
        · -- n < 539576
          rcases Nat.lt_or_ge n 359720 with hs4 | hs4
          · -- n < 359720
            rcases Nat.lt_or_ge n 179864 with hs5 | hs5
            · -- n < 179864
              exact Brocard.berndt_galway_chunk_0001 n m (by omega) (by omega) h
            · -- n >= 179864
              exact Brocard.berndt_galway_chunk_0002 n m (by omega) (by omega) h
          · -- n >= 359720
            exact Brocard.berndt_galway_chunk_0003 n m (by omega) (by omega) h
        · -- n >= 539576
          rcases Nat.lt_or_ge n 899288 with hs4 | hs4
          · -- n < 899288
            rcases Nat.lt_or_ge n 719432 with hs5 | hs5
            · -- n < 719432
              exact Brocard.berndt_galway_chunk_0004 n m (by omega) (by omega) h
            · -- n >= 719432
              exact Brocard.berndt_galway_chunk_0005 n m (by omega) (by omega) h
          · -- n >= 899288
            exact Brocard.berndt_galway_chunk_0006 n m (by omega) (by omega) h
      · -- n >= 1079144
        rcases Nat.lt_or_ge n 1618712 with hs3 | hs3
        · -- n < 1618712
          rcases Nat.lt_or_ge n 1438856 with hs4 | hs4
          · -- n < 1438856
            rcases Nat.lt_or_ge n 1259000 with hs5 | hs5
            · -- n < 1259000
              exact Brocard.berndt_galway_chunk_0007 n m (by omega) (by omega) h
            · -- n >= 1259000
              exact Brocard.berndt_galway_chunk_0008 n m (by omega) (by omega) h
          · -- n >= 1438856
            exact Brocard.berndt_galway_chunk_0009 n m (by omega) (by omega) h
        · -- n >= 1618712
          rcases Nat.lt_or_ge n 1978425 with hs4 | hs4
          · -- n < 1978425
            rcases Nat.lt_or_ge n 1798569 with hs5 | hs5
            · -- n < 1798569
              exact Brocard.berndt_galway_chunk_0010 n m (by omega) (by omega) h
            · -- n >= 1798569
              exact Brocard.berndt_galway_chunk_0011 n m (by omega) (by omega) h
          · -- n >= 1978425
            exact Brocard.berndt_galway_chunk_0012 n m (by omega) (by omega) h
    · -- n >= 2158281
      rcases Nat.lt_or_ge n 3237417 with hs2 | hs2
      · -- n < 3237417
        rcases Nat.lt_or_ge n 2697849 with hs3 | hs3
        · -- n < 2697849
          rcases Nat.lt_or_ge n 2517993 with hs4 | hs4
          · -- n < 2517993
            rcases Nat.lt_or_ge n 2338137 with hs5 | hs5
            · -- n < 2338137
              exact Brocard.berndt_galway_chunk_0013 n m (by omega) (by omega) h
            · -- n >= 2338137
              exact Brocard.berndt_galway_chunk_0014 n m (by omega) (by omega) h
          · -- n >= 2517993
            exact Brocard.berndt_galway_chunk_0015 n m (by omega) (by omega) h
        · -- n >= 2697849
          rcases Nat.lt_or_ge n 3057561 with hs4 | hs4
          · -- n < 3057561
            rcases Nat.lt_or_ge n 2877705 with hs5 | hs5
            · -- n < 2877705
              exact Brocard.berndt_galway_chunk_0016 n m (by omega) (by omega) h
            · -- n >= 2877705
              exact Brocard.berndt_galway_chunk_0017 n m (by omega) (by omega) h
          · -- n >= 3057561
            exact Brocard.berndt_galway_chunk_0018 n m (by omega) (by omega) h
      · -- n >= 3237417
        rcases Nat.lt_or_ge n 3776986 with hs3 | hs3
        · -- n < 3776986
          rcases Nat.lt_or_ge n 3597130 with hs4 | hs4
          · -- n < 3597130
            rcases Nat.lt_or_ge n 3417273 with hs5 | hs5
            · -- n < 3417273
              exact Brocard.berndt_galway_chunk_0019 n m (by omega) (by omega) h
            · -- n >= 3417273
              exact Brocard.berndt_galway_chunk_0020 n m (by omega) (by omega) h
          · -- n >= 3597130
            exact Brocard.berndt_galway_chunk_0021 n m (by omega) (by omega) h
        · -- n >= 3776986
          rcases Nat.lt_or_ge n 4136698 with hs4 | hs4
          · -- n < 4136698
            rcases Nat.lt_or_ge n 3956842 with hs5 | hs5
            · -- n < 3956842
              exact Brocard.berndt_galway_chunk_0022 n m (by omega) (by omega) h
            · -- n >= 3956842
              exact Brocard.berndt_galway_chunk_0023 n m (by omega) (by omega) h
          · -- n >= 4136698
            exact Brocard.berndt_galway_chunk_0024 n m (by omega) (by omega) h
  · -- n >= 4316554
    rcases Nat.lt_or_ge n 6474827 with hs1 | hs1
    · -- n < 6474827
      rcases Nat.lt_or_ge n 5395691 with hs2 | hs2
      · -- n < 5395691
        rcases Nat.lt_or_ge n 4856122 with hs3 | hs3
        · -- n < 4856122
          rcases Nat.lt_or_ge n 4676266 with hs4 | hs4
          · -- n < 4676266
            rcases Nat.lt_or_ge n 4496410 with hs5 | hs5
            · -- n < 4496410
              exact Brocard.berndt_galway_chunk_0025 n m (by omega) (by omega) h
            · -- n >= 4496410
              exact Brocard.berndt_galway_chunk_0026 n m (by omega) (by omega) h
          · -- n >= 4676266
            exact Brocard.berndt_galway_chunk_0027 n m (by omega) (by omega) h
        · -- n >= 4856122
          rcases Nat.lt_or_ge n 5215834 with hs4 | hs4
          · -- n < 5215834
            rcases Nat.lt_or_ge n 5035978 with hs5 | hs5
            · -- n < 5035978
              exact Brocard.berndt_galway_chunk_0028 n m (by omega) (by omega) h
            · -- n >= 5035978
              exact Brocard.berndt_galway_chunk_0029 n m (by omega) (by omega) h
          · -- n >= 5215834
            exact Brocard.berndt_galway_chunk_0030 n m (by omega) (by omega) h
      · -- n >= 5395691
        rcases Nat.lt_or_ge n 5935259 with hs3 | hs3
        · -- n < 5935259
          rcases Nat.lt_or_ge n 5755403 with hs4 | hs4
          · -- n < 5755403
            rcases Nat.lt_or_ge n 5575547 with hs5 | hs5
            · -- n < 5575547
              exact Brocard.berndt_galway_chunk_0031 n m (by omega) (by omega) h
            · -- n >= 5575547
              exact Brocard.berndt_galway_chunk_0032 n m (by omega) (by omega) h
          · -- n >= 5755403
            exact Brocard.berndt_galway_chunk_0033 n m (by omega) (by omega) h
        · -- n >= 5935259
          rcases Nat.lt_or_ge n 6294971 with hs4 | hs4
          · -- n < 6294971
            rcases Nat.lt_or_ge n 6115115 with hs5 | hs5
            · -- n < 6115115
              exact Brocard.berndt_galway_chunk_0034 n m (by omega) (by omega) h
            · -- n >= 6115115
              exact Brocard.berndt_galway_chunk_0035 n m (by omega) (by omega) h
          · -- n >= 6294971
            exact Brocard.berndt_galway_chunk_0036 n m (by omega) (by omega) h
    · -- n >= 6474827
      rcases Nat.lt_or_ge n 7553964 with hs2 | hs2
      · -- n < 7553964
        rcases Nat.lt_or_ge n 7014395 with hs3 | hs3
        · -- n < 7014395
          rcases Nat.lt_or_ge n 6834539 with hs4 | hs4
          · -- n < 6834539
            rcases Nat.lt_or_ge n 6654683 with hs5 | hs5
            · -- n < 6654683
              exact Brocard.berndt_galway_chunk_0037 n m (by omega) (by omega) h
            · -- n >= 6654683
              exact Brocard.berndt_galway_chunk_0038 n m (by omega) (by omega) h
          · -- n >= 6834539
            exact Brocard.berndt_galway_chunk_0039 n m (by omega) (by omega) h
        · -- n >= 7014395
          rcases Nat.lt_or_ge n 7374108 with hs4 | hs4
          · -- n < 7374108
            rcases Nat.lt_or_ge n 7194252 with hs5 | hs5
            · -- n < 7194252
              exact Brocard.berndt_galway_chunk_0040 n m (by omega) (by omega) h
            · -- n >= 7194252
              exact Brocard.berndt_galway_chunk_0041 n m (by omega) (by omega) h
          · -- n >= 7374108
            exact Brocard.berndt_galway_chunk_0042 n m (by omega) (by omega) h
      · -- n >= 7553964
        rcases Nat.lt_or_ge n 8093532 with hs3 | hs3
        · -- n < 8093532
          rcases Nat.lt_or_ge n 7913676 with hs4 | hs4
          · -- n < 7913676
            rcases Nat.lt_or_ge n 7733820 with hs5 | hs5
            · -- n < 7733820
              exact Brocard.berndt_galway_chunk_0043 n m (by omega) (by omega) h
            · -- n >= 7733820
              exact Brocard.berndt_galway_chunk_0044 n m (by omega) (by omega) h
          · -- n >= 7913676
            exact Brocard.berndt_galway_chunk_0045 n m (by omega) (by omega) h
        · -- n >= 8093532
          rcases Nat.lt_or_ge n 8273388 with hs4 | hs4
          · -- n < 8273388
            exact Brocard.berndt_galway_chunk_0046 n m (by omega) (by omega) h
          · -- n >= 8273388
            exact Brocard.berndt_galway_chunk_0047 n m (by omega) (by omega) h
