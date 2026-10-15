-- Prove2me | solution 1 for Brocard.berndt_galway_block_9
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:29:56.590711+00:00
-- url     : https://prove2.me/submissions/c347d4be-f3bb-44af-818a-d645ecfdf7ea

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_Brocard_berndt_galway_group_109
import Theorems.Thm_Brocard_berndt_galway_group_110
import Theorems.Thm_Brocard_berndt_galway_group_111
import Theorems.Thm_Brocard_berndt_galway_group_112
import Theorems.Thm_Brocard_berndt_galway_group_113
import Theorems.Thm_Brocard_berndt_galway_group_114
import Theorems.Thm_Brocard_berndt_galway_group_115
import Theorems.Thm_Brocard_berndt_galway_group_116
import Theorems.Thm_Brocard_berndt_galway_group_117
import Theorems.Thm_Brocard_berndt_galway_group_118
import Theorems.Thm_Brocard_berndt_galway_group_119
import Theorems.Thm_Brocard_berndt_galway_group_120

theorem solution (n m : ℕ) (h1 : 9 * 10 ^ 8 ≤ n) (h2 : n < 10 * 10 ^ 8)
    (h : Nat.factorial n + 1 = m ^ 2) : False := by
  have hA : (9 : ℕ) * 10 ^ 8 = 900000000 := by norm_num
  have hB : (10 : ℕ) * 10 ^ 8 = 1000000000 := by norm_num
  rw [hA] at h1
  rw [hB] at h2
  rcases Nat.lt_or_ge n 950359712 with hs0 | hs0
  · -- n < 950359712
    rcases Nat.lt_or_ge n 925359712 with hs1 | hs1
    · -- n < 925359712
      rcases Nat.lt_or_ge n 916906474 with hs2 | hs2
      · -- n < 916906474
        rcases Nat.lt_or_ge n 908453237 with hs3 | hs3
        · -- n < 908453237
          exact Brocard.berndt_galway_group_109 n m (by omega) (by omega) h
        · -- n >= 908453237
          exact Brocard.berndt_galway_group_110 n m (by omega) (by omega) h
      · -- n >= 916906474
        exact Brocard.berndt_galway_group_111 n m (by omega) (by omega) h
    · -- n >= 925359712
      rcases Nat.lt_or_ge n 942086330 with hs2 | hs2
      · -- n < 942086330
        rcases Nat.lt_or_ge n 933812949 with hs3 | hs3
        · -- n < 933812949
          exact Brocard.berndt_galway_group_112 n m (by omega) (by omega) h
        · -- n >= 933812949
          exact Brocard.berndt_galway_group_113 n m (by omega) (by omega) h
      · -- n >= 942086330
        exact Brocard.berndt_galway_group_114 n m (by omega) (by omega) h
  · -- n >= 950359712
    rcases Nat.lt_or_ge n 975179856 with hs1 | hs1
    · -- n < 975179856
      rcases Nat.lt_or_ge n 966906474 with hs2 | hs2
      · -- n < 966906474
        rcases Nat.lt_or_ge n 958633093 with hs3 | hs3
        · -- n < 958633093
          exact Brocard.berndt_galway_group_115 n m (by omega) (by omega) h
        · -- n >= 958633093
          exact Brocard.berndt_galway_group_116 n m (by omega) (by omega) h
      · -- n >= 966906474
        exact Brocard.berndt_galway_group_117 n m (by omega) (by omega) h
    · -- n >= 975179856
      rcases Nat.lt_or_ge n 991726618 with hs2 | hs2
      · -- n < 991726618
        rcases Nat.lt_or_ge n 983453237 with hs3 | hs3
        · -- n < 983453237
          exact Brocard.berndt_galway_group_118 n m (by omega) (by omega) h
        · -- n >= 983453237
          exact Brocard.berndt_galway_group_119 n m (by omega) (by omega) h
      · -- n >= 991726618
        exact Brocard.berndt_galway_group_120 n m (by omega) (by omega) h
