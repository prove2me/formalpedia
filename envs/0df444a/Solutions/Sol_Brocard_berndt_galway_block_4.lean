-- Prove2me | solution 1 for Brocard.berndt_galway_block_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:53:44.381852+00:00
-- url     : https://prove2.me/submissions/e5f557ff-9cd5-4f3d-af09-313cc79c3d6c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_Brocard_berndt_galway_group_049
import Theorems.Thm_Brocard_berndt_galway_group_050
import Theorems.Thm_Brocard_berndt_galway_group_051
import Theorems.Thm_Brocard_berndt_galway_group_052
import Theorems.Thm_Brocard_berndt_galway_group_053
import Theorems.Thm_Brocard_berndt_galway_group_054
import Theorems.Thm_Brocard_berndt_galway_group_055
import Theorems.Thm_Brocard_berndt_galway_group_056
import Theorems.Thm_Brocard_berndt_galway_group_057
import Theorems.Thm_Brocard_berndt_galway_group_058
import Theorems.Thm_Brocard_berndt_galway_group_059
import Theorems.Thm_Brocard_berndt_galway_group_060

theorem solution (n m : ℕ) (h1 : 4 * 10 ^ 8 ≤ n) (h2 : n < 5 * 10 ^ 8)
    (h : Nat.factorial n + 1 = m ^ 2) : False := by
  have hA : (4 : ℕ) * 10 ^ 8 = 400000000 := by norm_num
  have hB : (5 : ℕ) * 10 ^ 8 = 500000000 := by norm_num
  rw [hA] at h1
  rw [hB] at h2
  rcases Nat.lt_or_ge n 450359712 with hs0 | hs0
  · -- n < 450359712
    rcases Nat.lt_or_ge n 425359712 with hs1 | hs1
    · -- n < 425359712
      rcases Nat.lt_or_ge n 416906474 with hs2 | hs2
      · -- n < 416906474
        rcases Nat.lt_or_ge n 408453237 with hs3 | hs3
        · -- n < 408453237
          exact Brocard.berndt_galway_group_049 n m (by omega) (by omega) h
        · -- n >= 408453237
          exact Brocard.berndt_galway_group_050 n m (by omega) (by omega) h
      · -- n >= 416906474
        exact Brocard.berndt_galway_group_051 n m (by omega) (by omega) h
    · -- n >= 425359712
      rcases Nat.lt_or_ge n 442086330 with hs2 | hs2
      · -- n < 442086330
        rcases Nat.lt_or_ge n 433812949 with hs3 | hs3
        · -- n < 433812949
          exact Brocard.berndt_galway_group_052 n m (by omega) (by omega) h
        · -- n >= 433812949
          exact Brocard.berndt_galway_group_053 n m (by omega) (by omega) h
      · -- n >= 442086330
        exact Brocard.berndt_galway_group_054 n m (by omega) (by omega) h
  · -- n >= 450359712
    rcases Nat.lt_or_ge n 475179856 with hs1 | hs1
    · -- n < 475179856
      rcases Nat.lt_or_ge n 466906474 with hs2 | hs2
      · -- n < 466906474
        rcases Nat.lt_or_ge n 458633093 with hs3 | hs3
        · -- n < 458633093
          exact Brocard.berndt_galway_group_055 n m (by omega) (by omega) h
        · -- n >= 458633093
          exact Brocard.berndt_galway_group_056 n m (by omega) (by omega) h
      · -- n >= 466906474
        exact Brocard.berndt_galway_group_057 n m (by omega) (by omega) h
    · -- n >= 475179856
      rcases Nat.lt_or_ge n 491726618 with hs2 | hs2
      · -- n < 491726618
        rcases Nat.lt_or_ge n 483453237 with hs3 | hs3
        · -- n < 483453237
          exact Brocard.berndt_galway_group_058 n m (by omega) (by omega) h
        · -- n >= 483453237
          exact Brocard.berndt_galway_group_059 n m (by omega) (by omega) h
      · -- n >= 491726618
        exact Brocard.berndt_galway_group_060 n m (by omega) (by omega) h
