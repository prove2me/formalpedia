-- Prove2me | solution 1 for Brocard.berndt_galway_block_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:14:16.681314+00:00
-- url     : https://prove2.me/submissions/6b062ae0-6a2d-46a5-8e75-3ebe032f4d3c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_Brocard_berndt_galway_group_037
import Theorems.Thm_Brocard_berndt_galway_group_038
import Theorems.Thm_Brocard_berndt_galway_group_039
import Theorems.Thm_Brocard_berndt_galway_group_040
import Theorems.Thm_Brocard_berndt_galway_group_041
import Theorems.Thm_Brocard_berndt_galway_group_042
import Theorems.Thm_Brocard_berndt_galway_group_043
import Theorems.Thm_Brocard_berndt_galway_group_044
import Theorems.Thm_Brocard_berndt_galway_group_045
import Theorems.Thm_Brocard_berndt_galway_group_046
import Theorems.Thm_Brocard_berndt_galway_group_047
import Theorems.Thm_Brocard_berndt_galway_group_048

theorem solution (n m : ℕ) (h1 : 3 * 10 ^ 8 ≤ n) (h2 : n < 4 * 10 ^ 8)
    (h : Nat.factorial n + 1 = m ^ 2) : False := by
  have hA : (3 : ℕ) * 10 ^ 8 = 300000000 := by norm_num
  have hB : (4 : ℕ) * 10 ^ 8 = 400000000 := by norm_num
  rw [hA] at h1
  rw [hB] at h2
  rcases Nat.lt_or_ge n 350359712 with hs0 | hs0
  · -- n < 350359712
    rcases Nat.lt_or_ge n 325359712 with hs1 | hs1
    · -- n < 325359712
      rcases Nat.lt_or_ge n 316906474 with hs2 | hs2
      · -- n < 316906474
        rcases Nat.lt_or_ge n 308453237 with hs3 | hs3
        · -- n < 308453237
          exact Brocard.berndt_galway_group_037 n m (by omega) (by omega) h
        · -- n >= 308453237
          exact Brocard.berndt_galway_group_038 n m (by omega) (by omega) h
      · -- n >= 316906474
        exact Brocard.berndt_galway_group_039 n m (by omega) (by omega) h
    · -- n >= 325359712
      rcases Nat.lt_or_ge n 342086330 with hs2 | hs2
      · -- n < 342086330
        rcases Nat.lt_or_ge n 333812949 with hs3 | hs3
        · -- n < 333812949
          exact Brocard.berndt_galway_group_040 n m (by omega) (by omega) h
        · -- n >= 333812949
          exact Brocard.berndt_galway_group_041 n m (by omega) (by omega) h
      · -- n >= 342086330
        exact Brocard.berndt_galway_group_042 n m (by omega) (by omega) h
  · -- n >= 350359712
    rcases Nat.lt_or_ge n 375179856 with hs1 | hs1
    · -- n < 375179856
      rcases Nat.lt_or_ge n 366906474 with hs2 | hs2
      · -- n < 366906474
        rcases Nat.lt_or_ge n 358633093 with hs3 | hs3
        · -- n < 358633093
          exact Brocard.berndt_galway_group_043 n m (by omega) (by omega) h
        · -- n >= 358633093
          exact Brocard.berndt_galway_group_044 n m (by omega) (by omega) h
      · -- n >= 366906474
        exact Brocard.berndt_galway_group_045 n m (by omega) (by omega) h
    · -- n >= 375179856
      rcases Nat.lt_or_ge n 391726618 with hs2 | hs2
      · -- n < 391726618
        rcases Nat.lt_or_ge n 383453237 with hs3 | hs3
        · -- n < 383453237
          exact Brocard.berndt_galway_group_046 n m (by omega) (by omega) h
        · -- n >= 383453237
          exact Brocard.berndt_galway_group_047 n m (by omega) (by omega) h
      · -- n >= 391726618
        exact Brocard.berndt_galway_group_048 n m (by omega) (by omega) h
