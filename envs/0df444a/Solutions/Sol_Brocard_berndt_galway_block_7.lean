-- Prove2me | solution 1 for Brocard.berndt_galway_block_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:50:35.579558+00:00
-- url     : https://prove2.me/submissions/5a96c14b-046e-483b-bc89-42f634f56464

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_Brocard_berndt_galway_group_085
import Theorems.Thm_Brocard_berndt_galway_group_086
import Theorems.Thm_Brocard_berndt_galway_group_087
import Theorems.Thm_Brocard_berndt_galway_group_088
import Theorems.Thm_Brocard_berndt_galway_group_089
import Theorems.Thm_Brocard_berndt_galway_group_090
import Theorems.Thm_Brocard_berndt_galway_group_091
import Theorems.Thm_Brocard_berndt_galway_group_092
import Theorems.Thm_Brocard_berndt_galway_group_093
import Theorems.Thm_Brocard_berndt_galway_group_094
import Theorems.Thm_Brocard_berndt_galway_group_095
import Theorems.Thm_Brocard_berndt_galway_group_096

theorem solution (n m : ℕ) (h1 : 7 * 10 ^ 8 ≤ n) (h2 : n < 8 * 10 ^ 8)
    (h : Nat.factorial n + 1 = m ^ 2) : False := by
  have hA : (7 : ℕ) * 10 ^ 8 = 700000000 := by norm_num
  have hB : (8 : ℕ) * 10 ^ 8 = 800000000 := by norm_num
  rw [hA] at h1
  rw [hB] at h2
  rcases Nat.lt_or_ge n 750359712 with hs0 | hs0
  · -- n < 750359712
    rcases Nat.lt_or_ge n 725359712 with hs1 | hs1
    · -- n < 725359712
      rcases Nat.lt_or_ge n 716906474 with hs2 | hs2
      · -- n < 716906474
        rcases Nat.lt_or_ge n 708453237 with hs3 | hs3
        · -- n < 708453237
          exact Brocard.berndt_galway_group_085 n m (by omega) (by omega) h
        · -- n >= 708453237
          exact Brocard.berndt_galway_group_086 n m (by omega) (by omega) h
      · -- n >= 716906474
        exact Brocard.berndt_galway_group_087 n m (by omega) (by omega) h
    · -- n >= 725359712
      rcases Nat.lt_or_ge n 742086330 with hs2 | hs2
      · -- n < 742086330
        rcases Nat.lt_or_ge n 733812949 with hs3 | hs3
        · -- n < 733812949
          exact Brocard.berndt_galway_group_088 n m (by omega) (by omega) h
        · -- n >= 733812949
          exact Brocard.berndt_galway_group_089 n m (by omega) (by omega) h
      · -- n >= 742086330
        exact Brocard.berndt_galway_group_090 n m (by omega) (by omega) h
  · -- n >= 750359712
    rcases Nat.lt_or_ge n 775179856 with hs1 | hs1
    · -- n < 775179856
      rcases Nat.lt_or_ge n 766906474 with hs2 | hs2
      · -- n < 766906474
        rcases Nat.lt_or_ge n 758633093 with hs3 | hs3
        · -- n < 758633093
          exact Brocard.berndt_galway_group_091 n m (by omega) (by omega) h
        · -- n >= 758633093
          exact Brocard.berndt_galway_group_092 n m (by omega) (by omega) h
      · -- n >= 766906474
        exact Brocard.berndt_galway_group_093 n m (by omega) (by omega) h
    · -- n >= 775179856
      rcases Nat.lt_or_ge n 791726618 with hs2 | hs2
      · -- n < 791726618
        rcases Nat.lt_or_ge n 783453237 with hs3 | hs3
        · -- n < 783453237
          exact Brocard.berndt_galway_group_094 n m (by omega) (by omega) h
        · -- n >= 783453237
          exact Brocard.berndt_galway_group_095 n m (by omega) (by omega) h
      · -- n >= 791726618
        exact Brocard.berndt_galway_group_096 n m (by omega) (by omega) h
