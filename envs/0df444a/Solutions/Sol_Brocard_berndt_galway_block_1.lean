-- Prove2me | solution 1 for Brocard.berndt_galway_block_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:28:33.276836+00:00
-- url     : https://prove2.me/submissions/42a615e1-6a93-4eb4-92b5-e84673f5daf6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_Brocard_berndt_galway_group_013
import Theorems.Thm_Brocard_berndt_galway_group_014
import Theorems.Thm_Brocard_berndt_galway_group_015
import Theorems.Thm_Brocard_berndt_galway_group_016
import Theorems.Thm_Brocard_berndt_galway_group_017
import Theorems.Thm_Brocard_berndt_galway_group_018
import Theorems.Thm_Brocard_berndt_galway_group_019
import Theorems.Thm_Brocard_berndt_galway_group_020
import Theorems.Thm_Brocard_berndt_galway_group_021
import Theorems.Thm_Brocard_berndt_galway_group_022
import Theorems.Thm_Brocard_berndt_galway_group_023
import Theorems.Thm_Brocard_berndt_galway_group_024

theorem solution (n m : ℕ) (h1 : 1 * 10 ^ 8 ≤ n) (h2 : n < 2 * 10 ^ 8)
    (h : Nat.factorial n + 1 = m ^ 2) : False := by
  have hA : (1 : ℕ) * 10 ^ 8 = 100000000 := by norm_num
  have hB : (2 : ℕ) * 10 ^ 8 = 200000000 := by norm_num
  rw [hA] at h1
  rw [hB] at h2
  rcases Nat.lt_or_ge n 150359712 with hs0 | hs0
  · -- n < 150359712
    rcases Nat.lt_or_ge n 125359712 with hs1 | hs1
    · -- n < 125359712
      rcases Nat.lt_or_ge n 116906474 with hs2 | hs2
      · -- n < 116906474
        rcases Nat.lt_or_ge n 108453237 with hs3 | hs3
        · -- n < 108453237
          exact Brocard.berndt_galway_group_013 n m (by omega) (by omega) h
        · -- n >= 108453237
          exact Brocard.berndt_galway_group_014 n m (by omega) (by omega) h
      · -- n >= 116906474
        exact Brocard.berndt_galway_group_015 n m (by omega) (by omega) h
    · -- n >= 125359712
      rcases Nat.lt_or_ge n 142086330 with hs2 | hs2
      · -- n < 142086330
        rcases Nat.lt_or_ge n 133812949 with hs3 | hs3
        · -- n < 133812949
          exact Brocard.berndt_galway_group_016 n m (by omega) (by omega) h
        · -- n >= 133812949
          exact Brocard.berndt_galway_group_017 n m (by omega) (by omega) h
      · -- n >= 142086330
        exact Brocard.berndt_galway_group_018 n m (by omega) (by omega) h
  · -- n >= 150359712
    rcases Nat.lt_or_ge n 175179856 with hs1 | hs1
    · -- n < 175179856
      rcases Nat.lt_or_ge n 166906474 with hs2 | hs2
      · -- n < 166906474
        rcases Nat.lt_or_ge n 158633093 with hs3 | hs3
        · -- n < 158633093
          exact Brocard.berndt_galway_group_019 n m (by omega) (by omega) h
        · -- n >= 158633093
          exact Brocard.berndt_galway_group_020 n m (by omega) (by omega) h
      · -- n >= 166906474
        exact Brocard.berndt_galway_group_021 n m (by omega) (by omega) h
    · -- n >= 175179856
      rcases Nat.lt_or_ge n 191726618 with hs2 | hs2
      · -- n < 191726618
        rcases Nat.lt_or_ge n 183453237 with hs3 | hs3
        · -- n < 183453237
          exact Brocard.berndt_galway_group_022 n m (by omega) (by omega) h
        · -- n >= 183453237
          exact Brocard.berndt_galway_group_023 n m (by omega) (by omega) h
      · -- n >= 191726618
        exact Brocard.berndt_galway_group_024 n m (by omega) (by omega) h
