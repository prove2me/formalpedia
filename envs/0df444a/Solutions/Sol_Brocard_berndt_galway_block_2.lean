-- Prove2me | solution 1 for Brocard.berndt_galway_block_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:16:06.198711+00:00
-- url     : https://prove2.me/submissions/ccd656df-69eb-454c-a007-b6153132d76f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_Brocard_berndt_galway_group_025
import Theorems.Thm_Brocard_berndt_galway_group_026
import Theorems.Thm_Brocard_berndt_galway_group_027
import Theorems.Thm_Brocard_berndt_galway_group_028
import Theorems.Thm_Brocard_berndt_galway_group_029
import Theorems.Thm_Brocard_berndt_galway_group_030
import Theorems.Thm_Brocard_berndt_galway_group_031
import Theorems.Thm_Brocard_berndt_galway_group_032
import Theorems.Thm_Brocard_berndt_galway_group_033
import Theorems.Thm_Brocard_berndt_galway_group_034
import Theorems.Thm_Brocard_berndt_galway_group_035
import Theorems.Thm_Brocard_berndt_galway_group_036

theorem solution (n m : ℕ) (h1 : 2 * 10 ^ 8 ≤ n) (h2 : n < 3 * 10 ^ 8)
    (h : Nat.factorial n + 1 = m ^ 2) : False := by
  have hA : (2 : ℕ) * 10 ^ 8 = 200000000 := by norm_num
  have hB : (3 : ℕ) * 10 ^ 8 = 300000000 := by norm_num
  rw [hA] at h1
  rw [hB] at h2
  rcases Nat.lt_or_ge n 250359712 with hs0 | hs0
  · -- n < 250359712
    rcases Nat.lt_or_ge n 225359712 with hs1 | hs1
    · -- n < 225359712
      rcases Nat.lt_or_ge n 216906474 with hs2 | hs2
      · -- n < 216906474
        rcases Nat.lt_or_ge n 208453237 with hs3 | hs3
        · -- n < 208453237
          exact Brocard.berndt_galway_group_025 n m (by omega) (by omega) h
        · -- n >= 208453237
          exact Brocard.berndt_galway_group_026 n m (by omega) (by omega) h
      · -- n >= 216906474
        exact Brocard.berndt_galway_group_027 n m (by omega) (by omega) h
    · -- n >= 225359712
      rcases Nat.lt_or_ge n 242086330 with hs2 | hs2
      · -- n < 242086330
        rcases Nat.lt_or_ge n 233812949 with hs3 | hs3
        · -- n < 233812949
          exact Brocard.berndt_galway_group_028 n m (by omega) (by omega) h
        · -- n >= 233812949
          exact Brocard.berndt_galway_group_029 n m (by omega) (by omega) h
      · -- n >= 242086330
        exact Brocard.berndt_galway_group_030 n m (by omega) (by omega) h
  · -- n >= 250359712
    rcases Nat.lt_or_ge n 275179856 with hs1 | hs1
    · -- n < 275179856
      rcases Nat.lt_or_ge n 266906474 with hs2 | hs2
      · -- n < 266906474
        rcases Nat.lt_or_ge n 258633093 with hs3 | hs3
        · -- n < 258633093
          exact Brocard.berndt_galway_group_031 n m (by omega) (by omega) h
        · -- n >= 258633093
          exact Brocard.berndt_galway_group_032 n m (by omega) (by omega) h
      · -- n >= 266906474
        exact Brocard.berndt_galway_group_033 n m (by omega) (by omega) h
    · -- n >= 275179856
      rcases Nat.lt_or_ge n 291726618 with hs2 | hs2
      · -- n < 291726618
        rcases Nat.lt_or_ge n 283453237 with hs3 | hs3
        · -- n < 283453237
          exact Brocard.berndt_galway_group_034 n m (by omega) (by omega) h
        · -- n >= 283453237
          exact Brocard.berndt_galway_group_035 n m (by omega) (by omega) h
      · -- n >= 291726618
        exact Brocard.berndt_galway_group_036 n m (by omega) (by omega) h
