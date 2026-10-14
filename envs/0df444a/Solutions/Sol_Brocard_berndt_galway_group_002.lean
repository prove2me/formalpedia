-- Prove2me | solution 1 for Brocard.berndt_galway_group_002
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:55:07.15284+00:00
-- url     : https://prove2.me/submissions/c364f34e-56e3-4ed7-904a-933ffb6bc7a6

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_0048
import Theorems.Thm_Brocard_berndt_galway_chunk_0049
import Theorems.Thm_Brocard_berndt_galway_chunk_0050
import Theorems.Thm_Brocard_berndt_galway_chunk_0051
import Theorems.Thm_Brocard_berndt_galway_chunk_0052
import Theorems.Thm_Brocard_berndt_galway_chunk_0053
import Theorems.Thm_Brocard_berndt_galway_chunk_0054
import Theorems.Thm_Brocard_berndt_galway_chunk_0055
import Theorems.Thm_Brocard_berndt_galway_chunk_0056
import Theorems.Thm_Brocard_berndt_galway_chunk_0057
import Theorems.Thm_Brocard_berndt_galway_chunk_0058
import Theorems.Thm_Brocard_berndt_galway_chunk_0059
import Theorems.Thm_Brocard_berndt_galway_chunk_0060
import Theorems.Thm_Brocard_berndt_galway_chunk_0061
import Theorems.Thm_Brocard_berndt_galway_chunk_0062
import Theorems.Thm_Brocard_berndt_galway_chunk_0063
import Theorems.Thm_Brocard_berndt_galway_chunk_0064
import Theorems.Thm_Brocard_berndt_galway_chunk_0065
import Theorems.Thm_Brocard_berndt_galway_chunk_0066
import Theorems.Thm_Brocard_berndt_galway_chunk_0067
import Theorems.Thm_Brocard_berndt_galway_chunk_0068
import Theorems.Thm_Brocard_berndt_galway_chunk_0069
import Theorems.Thm_Brocard_berndt_galway_chunk_0070
import Theorems.Thm_Brocard_berndt_galway_chunk_0071
import Theorems.Thm_Brocard_berndt_galway_chunk_0072
import Theorems.Thm_Brocard_berndt_galway_chunk_0073
import Theorems.Thm_Brocard_berndt_galway_chunk_0074
import Theorems.Thm_Brocard_berndt_galway_chunk_0075
import Theorems.Thm_Brocard_berndt_galway_chunk_0076
import Theorems.Thm_Brocard_berndt_galway_chunk_0077
import Theorems.Thm_Brocard_berndt_galway_chunk_0078
import Theorems.Thm_Brocard_berndt_galway_chunk_0079
import Theorems.Thm_Brocard_berndt_galway_chunk_0080
import Theorems.Thm_Brocard_berndt_galway_chunk_0081
import Theorems.Thm_Brocard_berndt_galway_chunk_0082
import Theorems.Thm_Brocard_berndt_galway_chunk_0083
import Theorems.Thm_Brocard_berndt_galway_chunk_0084
import Theorems.Thm_Brocard_berndt_galway_chunk_0085
import Theorems.Thm_Brocard_berndt_galway_chunk_0086
import Theorems.Thm_Brocard_berndt_galway_chunk_0087
import Theorems.Thm_Brocard_berndt_galway_chunk_0088
import Theorems.Thm_Brocard_berndt_galway_chunk_0089
import Theorems.Thm_Brocard_berndt_galway_chunk_0090
import Theorems.Thm_Brocard_berndt_galway_chunk_0091
import Theorems.Thm_Brocard_berndt_galway_chunk_0092
import Theorems.Thm_Brocard_berndt_galway_chunk_0093
import Theorems.Thm_Brocard_berndt_galway_chunk_0094

theorem solution (n m : ℕ) (h1 : 8453244 ≤ n) (h2 : n < 16906481) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 12769791 with hs0 | hs0
  · -- n < 12769791
    rcases Nat.lt_or_ge n 10611517 with hs1 | hs1
    · -- n < 10611517
      rcases Nat.lt_or_ge n 9532381 with hs2 | hs2
      · -- n < 9532381
        rcases Nat.lt_or_ge n 8992813 with hs3 | hs3
        · -- n < 8992813
          rcases Nat.lt_or_ge n 8812956 with hs4 | hs4
          · -- n < 8812956
            rcases Nat.lt_or_ge n 8633100 with hs5 | hs5
            · -- n < 8633100
              exact Brocard.berndt_galway_chunk_0048 n m (by omega) (by omega) h
            · -- n >= 8633100
              exact Brocard.berndt_galway_chunk_0049 n m (by omega) (by omega) h
          · -- n >= 8812956
            exact Brocard.berndt_galway_chunk_0050 n m (by omega) (by omega) h
        · -- n >= 8992813
          rcases Nat.lt_or_ge n 9352525 with hs4 | hs4
          · -- n < 9352525
            rcases Nat.lt_or_ge n 9172669 with hs5 | hs5
            · -- n < 9172669
              exact Brocard.berndt_galway_chunk_0051 n m (by omega) (by omega) h
            · -- n >= 9172669
              exact Brocard.berndt_galway_chunk_0052 n m (by omega) (by omega) h
          · -- n >= 9352525
            exact Brocard.berndt_galway_chunk_0053 n m (by omega) (by omega) h
      · -- n >= 9532381
        rcases Nat.lt_or_ge n 10071949 with hs3 | hs3
        · -- n < 10071949
          rcases Nat.lt_or_ge n 9892093 with hs4 | hs4
          · -- n < 9892093
            rcases Nat.lt_or_ge n 9712237 with hs5 | hs5
            · -- n < 9712237
              exact Brocard.berndt_galway_chunk_0054 n m (by omega) (by omega) h
            · -- n >= 9712237
              exact Brocard.berndt_galway_chunk_0055 n m (by omega) (by omega) h
          · -- n >= 9892093
            exact Brocard.berndt_galway_chunk_0056 n m (by omega) (by omega) h
        · -- n >= 10071949
          rcases Nat.lt_or_ge n 10431661 with hs4 | hs4
          · -- n < 10431661
            rcases Nat.lt_or_ge n 10251805 with hs5 | hs5
            · -- n < 10251805
              exact Brocard.berndt_galway_chunk_0057 n m (by omega) (by omega) h
            · -- n >= 10251805
              exact Brocard.berndt_galway_chunk_0058 n m (by omega) (by omega) h
          · -- n >= 10431661
            exact Brocard.berndt_galway_chunk_0059 n m (by omega) (by omega) h
    · -- n >= 10611517
      rcases Nat.lt_or_ge n 11690654 with hs2 | hs2
      · -- n < 11690654
        rcases Nat.lt_or_ge n 11151086 with hs3 | hs3
        · -- n < 11151086
          rcases Nat.lt_or_ge n 10971230 with hs4 | hs4
          · -- n < 10971230
            rcases Nat.lt_or_ge n 10791374 with hs5 | hs5
            · -- n < 10791374
              exact Brocard.berndt_galway_chunk_0060 n m (by omega) (by omega) h
            · -- n >= 10791374
              exact Brocard.berndt_galway_chunk_0061 n m (by omega) (by omega) h
          · -- n >= 10971230
            exact Brocard.berndt_galway_chunk_0062 n m (by omega) (by omega) h
        · -- n >= 11151086
          rcases Nat.lt_or_ge n 11510798 with hs4 | hs4
          · -- n < 11510798
            rcases Nat.lt_or_ge n 11330942 with hs5 | hs5
            · -- n < 11330942
              exact Brocard.berndt_galway_chunk_0063 n m (by omega) (by omega) h
            · -- n >= 11330942
              exact Brocard.berndt_galway_chunk_0064 n m (by omega) (by omega) h
          · -- n >= 11510798
            exact Brocard.berndt_galway_chunk_0065 n m (by omega) (by omega) h
      · -- n >= 11690654
        rcases Nat.lt_or_ge n 12230222 with hs3 | hs3
        · -- n < 12230222
          rcases Nat.lt_or_ge n 12050366 with hs4 | hs4
          · -- n < 12050366
            rcases Nat.lt_or_ge n 11870510 with hs5 | hs5
            · -- n < 11870510
              exact Brocard.berndt_galway_chunk_0066 n m (by omega) (by omega) h
            · -- n >= 11870510
              exact Brocard.berndt_galway_chunk_0067 n m (by omega) (by omega) h
          · -- n >= 12050366
            exact Brocard.berndt_galway_chunk_0068 n m (by omega) (by omega) h
        · -- n >= 12230222
          rcases Nat.lt_or_ge n 12589935 with hs4 | hs4
          · -- n < 12589935
            rcases Nat.lt_or_ge n 12410078 with hs5 | hs5
            · -- n < 12410078
              exact Brocard.berndt_galway_chunk_0069 n m (by omega) (by omega) h
            · -- n >= 12410078
              exact Brocard.berndt_galway_chunk_0070 n m (by omega) (by omega) h
          · -- n >= 12589935
            exact Brocard.berndt_galway_chunk_0071 n m (by omega) (by omega) h
  · -- n >= 12769791
    rcases Nat.lt_or_ge n 14928064 with hs1 | hs1
    · -- n < 14928064
      rcases Nat.lt_or_ge n 13848927 with hs2 | hs2
      · -- n < 13848927
        rcases Nat.lt_or_ge n 13309359 with hs3 | hs3
        · -- n < 13309359
          rcases Nat.lt_or_ge n 13129503 with hs4 | hs4
          · -- n < 13129503
            rcases Nat.lt_or_ge n 12949647 with hs5 | hs5
            · -- n < 12949647
              exact Brocard.berndt_galway_chunk_0072 n m (by omega) (by omega) h
            · -- n >= 12949647
              exact Brocard.berndt_galway_chunk_0073 n m (by omega) (by omega) h
          · -- n >= 13129503
            exact Brocard.berndt_galway_chunk_0074 n m (by omega) (by omega) h
        · -- n >= 13309359
          rcases Nat.lt_or_ge n 13669071 with hs4 | hs4
          · -- n < 13669071
            rcases Nat.lt_or_ge n 13489215 with hs5 | hs5
            · -- n < 13489215
              exact Brocard.berndt_galway_chunk_0075 n m (by omega) (by omega) h
            · -- n >= 13489215
              exact Brocard.berndt_galway_chunk_0076 n m (by omega) (by omega) h
          · -- n >= 13669071
            exact Brocard.berndt_galway_chunk_0077 n m (by omega) (by omega) h
      · -- n >= 13848927
        rcases Nat.lt_or_ge n 14388496 with hs3 | hs3
        · -- n < 14388496
          rcases Nat.lt_or_ge n 14208639 with hs4 | hs4
          · -- n < 14208639
            rcases Nat.lt_or_ge n 14028783 with hs5 | hs5
            · -- n < 14028783
              exact Brocard.berndt_galway_chunk_0078 n m (by omega) (by omega) h
            · -- n >= 14028783
              exact Brocard.berndt_galway_chunk_0079 n m (by omega) (by omega) h
          · -- n >= 14208639
            exact Brocard.berndt_galway_chunk_0080 n m (by omega) (by omega) h
        · -- n >= 14388496
          rcases Nat.lt_or_ge n 14748208 with hs4 | hs4
          · -- n < 14748208
            rcases Nat.lt_or_ge n 14568352 with hs5 | hs5
            · -- n < 14568352
              exact Brocard.berndt_galway_chunk_0081 n m (by omega) (by omega) h
            · -- n >= 14568352
              exact Brocard.berndt_galway_chunk_0082 n m (by omega) (by omega) h
          · -- n >= 14748208
            exact Brocard.berndt_galway_chunk_0083 n m (by omega) (by omega) h
    · -- n >= 14928064
      rcases Nat.lt_or_ge n 16007200 with hs2 | hs2
      · -- n < 16007200
        rcases Nat.lt_or_ge n 15467632 with hs3 | hs3
        · -- n < 15467632
          rcases Nat.lt_or_ge n 15287776 with hs4 | hs4
          · -- n < 15287776
            rcases Nat.lt_or_ge n 15107920 with hs5 | hs5
            · -- n < 15107920
              exact Brocard.berndt_galway_chunk_0084 n m (by omega) (by omega) h
            · -- n >= 15107920
              exact Brocard.berndt_galway_chunk_0085 n m (by omega) (by omega) h
          · -- n >= 15287776
            exact Brocard.berndt_galway_chunk_0086 n m (by omega) (by omega) h
        · -- n >= 15467632
          rcases Nat.lt_or_ge n 15827344 with hs4 | hs4
          · -- n < 15827344
            rcases Nat.lt_or_ge n 15647488 with hs5 | hs5
            · -- n < 15647488
              exact Brocard.berndt_galway_chunk_0087 n m (by omega) (by omega) h
            · -- n >= 15647488
              exact Brocard.berndt_galway_chunk_0088 n m (by omega) (by omega) h
          · -- n >= 15827344
            exact Brocard.berndt_galway_chunk_0089 n m (by omega) (by omega) h
      · -- n >= 16007200
        rcases Nat.lt_or_ge n 16546769 with hs3 | hs3
        · -- n < 16546769
          rcases Nat.lt_or_ge n 16366913 with hs4 | hs4
          · -- n < 16366913
            rcases Nat.lt_or_ge n 16187057 with hs5 | hs5
            · -- n < 16187057
              exact Brocard.berndt_galway_chunk_0090 n m (by omega) (by omega) h
            · -- n >= 16187057
              exact Brocard.berndt_galway_chunk_0091 n m (by omega) (by omega) h
          · -- n >= 16366913
            exact Brocard.berndt_galway_chunk_0092 n m (by omega) (by omega) h
        · -- n >= 16546769
          rcases Nat.lt_or_ge n 16726625 with hs4 | hs4
          · -- n < 16726625
            exact Brocard.berndt_galway_chunk_0093 n m (by omega) (by omega) h
          · -- n >= 16726625
            exact Brocard.berndt_galway_chunk_0094 n m (by omega) (by omega) h
