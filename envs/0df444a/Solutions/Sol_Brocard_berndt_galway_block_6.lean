-- Prove2me | solution 1 for Brocard.berndt_galway_block_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:10:40.191987+00:00
-- url     : https://prove2.me/submissions/2b86426a-313e-40d8-9253-bc4952d94b0e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_Brocard_berndt_galway_group_073
import Theorems.Thm_Brocard_berndt_galway_group_074
import Theorems.Thm_Brocard_berndt_galway_group_075
import Theorems.Thm_Brocard_berndt_galway_group_076
import Theorems.Thm_Brocard_berndt_galway_group_077
import Theorems.Thm_Brocard_berndt_galway_group_078
import Theorems.Thm_Brocard_berndt_galway_group_079
import Theorems.Thm_Brocard_berndt_galway_group_080
import Theorems.Thm_Brocard_berndt_galway_group_081
import Theorems.Thm_Brocard_berndt_galway_group_082
import Theorems.Thm_Brocard_berndt_galway_group_083
import Theorems.Thm_Brocard_berndt_galway_group_084

theorem solution (n m : ℕ) (h1 : 6 * 10 ^ 8 ≤ n) (h2 : n < 7 * 10 ^ 8)
    (h : Nat.factorial n + 1 = m ^ 2) : False := by
  have hA : (6 : ℕ) * 10 ^ 8 = 600000000 := by norm_num
  have hB : (7 : ℕ) * 10 ^ 8 = 700000000 := by norm_num
  rw [hA] at h1
  rw [hB] at h2
  rcases Nat.lt_or_ge n 650359712 with hs0 | hs0
  · -- n < 650359712
    rcases Nat.lt_or_ge n 625359712 with hs1 | hs1
    · -- n < 625359712
      rcases Nat.lt_or_ge n 616906474 with hs2 | hs2
      · -- n < 616906474
        rcases Nat.lt_or_ge n 608453237 with hs3 | hs3
        · -- n < 608453237
          exact Brocard.berndt_galway_group_073 n m (by omega) (by omega) h
        · -- n >= 608453237
          exact Brocard.berndt_galway_group_074 n m (by omega) (by omega) h
      · -- n >= 616906474
        exact Brocard.berndt_galway_group_075 n m (by omega) (by omega) h
    · -- n >= 625359712
      rcases Nat.lt_or_ge n 642086330 with hs2 | hs2
      · -- n < 642086330
        rcases Nat.lt_or_ge n 633812949 with hs3 | hs3
        · -- n < 633812949
          exact Brocard.berndt_galway_group_076 n m (by omega) (by omega) h
        · -- n >= 633812949
          exact Brocard.berndt_galway_group_077 n m (by omega) (by omega) h
      · -- n >= 642086330
        exact Brocard.berndt_galway_group_078 n m (by omega) (by omega) h
  · -- n >= 650359712
    rcases Nat.lt_or_ge n 675179856 with hs1 | hs1
    · -- n < 675179856
      rcases Nat.lt_or_ge n 666906474 with hs2 | hs2
      · -- n < 666906474
        rcases Nat.lt_or_ge n 658633093 with hs3 | hs3
        · -- n < 658633093
          exact Brocard.berndt_galway_group_079 n m (by omega) (by omega) h
        · -- n >= 658633093
          exact Brocard.berndt_galway_group_080 n m (by omega) (by omega) h
      · -- n >= 666906474
        exact Brocard.berndt_galway_group_081 n m (by omega) (by omega) h
    · -- n >= 675179856
      rcases Nat.lt_or_ge n 691726618 with hs2 | hs2
      · -- n < 691726618
        rcases Nat.lt_or_ge n 683453237 with hs3 | hs3
        · -- n < 683453237
          exact Brocard.berndt_galway_group_082 n m (by omega) (by omega) h
        · -- n >= 683453237
          exact Brocard.berndt_galway_group_083 n m (by omega) (by omega) h
      · -- n >= 691726618
        exact Brocard.berndt_galway_group_084 n m (by omega) (by omega) h
