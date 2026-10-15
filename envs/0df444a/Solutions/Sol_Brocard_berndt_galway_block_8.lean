-- Prove2me | solution 1 for Brocard.berndt_galway_block_8
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:44:05.908658+00:00
-- url     : https://prove2.me/submissions/8e86752e-e84a-403e-970c-793de61f1f0f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_Brocard_berndt_galway_group_097
import Theorems.Thm_Brocard_berndt_galway_group_098
import Theorems.Thm_Brocard_berndt_galway_group_099
import Theorems.Thm_Brocard_berndt_galway_group_100
import Theorems.Thm_Brocard_berndt_galway_group_101
import Theorems.Thm_Brocard_berndt_galway_group_102
import Theorems.Thm_Brocard_berndt_galway_group_103
import Theorems.Thm_Brocard_berndt_galway_group_104
import Theorems.Thm_Brocard_berndt_galway_group_105
import Theorems.Thm_Brocard_berndt_galway_group_106
import Theorems.Thm_Brocard_berndt_galway_group_107
import Theorems.Thm_Brocard_berndt_galway_group_108

theorem solution (n m : ℕ) (h1 : 8 * 10 ^ 8 ≤ n) (h2 : n < 9 * 10 ^ 8)
    (h : Nat.factorial n + 1 = m ^ 2) : False := by
  have hA : (8 : ℕ) * 10 ^ 8 = 800000000 := by norm_num
  have hB : (9 : ℕ) * 10 ^ 8 = 900000000 := by norm_num
  rw [hA] at h1
  rw [hB] at h2
  rcases Nat.lt_or_ge n 850359712 with hs0 | hs0
  · -- n < 850359712
    rcases Nat.lt_or_ge n 825359712 with hs1 | hs1
    · -- n < 825359712
      rcases Nat.lt_or_ge n 816906474 with hs2 | hs2
      · -- n < 816906474
        rcases Nat.lt_or_ge n 808453237 with hs3 | hs3
        · -- n < 808453237
          exact Brocard.berndt_galway_group_097 n m (by omega) (by omega) h
        · -- n >= 808453237
          exact Brocard.berndt_galway_group_098 n m (by omega) (by omega) h
      · -- n >= 816906474
        exact Brocard.berndt_galway_group_099 n m (by omega) (by omega) h
    · -- n >= 825359712
      rcases Nat.lt_or_ge n 842086330 with hs2 | hs2
      · -- n < 842086330
        rcases Nat.lt_or_ge n 833812949 with hs3 | hs3
        · -- n < 833812949
          exact Brocard.berndt_galway_group_100 n m (by omega) (by omega) h
        · -- n >= 833812949
          exact Brocard.berndt_galway_group_101 n m (by omega) (by omega) h
      · -- n >= 842086330
        exact Brocard.berndt_galway_group_102 n m (by omega) (by omega) h
  · -- n >= 850359712
    rcases Nat.lt_or_ge n 875179856 with hs1 | hs1
    · -- n < 875179856
      rcases Nat.lt_or_ge n 866906474 with hs2 | hs2
      · -- n < 866906474
        rcases Nat.lt_or_ge n 858633093 with hs3 | hs3
        · -- n < 858633093
          exact Brocard.berndt_galway_group_103 n m (by omega) (by omega) h
        · -- n >= 858633093
          exact Brocard.berndt_galway_group_104 n m (by omega) (by omega) h
      · -- n >= 866906474
        exact Brocard.berndt_galway_group_105 n m (by omega) (by omega) h
    · -- n >= 875179856
      rcases Nat.lt_or_ge n 891726618 with hs2 | hs2
      · -- n < 891726618
        rcases Nat.lt_or_ge n 883453237 with hs3 | hs3
        · -- n < 883453237
          exact Brocard.berndt_galway_group_106 n m (by omega) (by omega) h
        · -- n >= 883453237
          exact Brocard.berndt_galway_group_107 n m (by omega) (by omega) h
      · -- n >= 891726618
        exact Brocard.berndt_galway_group_108 n m (by omega) (by omega) h
