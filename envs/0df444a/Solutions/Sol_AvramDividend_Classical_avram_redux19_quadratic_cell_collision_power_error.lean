-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux19_quadratic_cell_collision_power_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:57:39.891129+00:00
-- url     : https://prove2.me/submissions/efa6e57d-4afd-444b-ac2f-4852bb80e8c1

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_avram_redux19_unit_interval_power_lipschitz
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-! A quadratic short-cell error becomes an inverse-mesh product error. -/
theorem solution
    (a b C : ℝ) (n : ℕ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hC : 0 ≤ C)
    (hgap : b - a ≤ C / ((n + 1 : ℕ) : ℝ) ^ 2) :
    0 ≤ b ^ (n + 1) - a ^ (n + 1) ∧
      b ^ (n + 1) - a ^ (n + 1) ≤ C / ((n + 1 : ℕ) : ℝ) := by
  have hpower := AvramDividend.Classical.avram_redux19_unit_interval_power_lipschitz
    a b (n + 1) ha hab hb
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  constructor
  · exact hpower.1
  · calc
      b ^ (n + 1) - a ^ (n + 1) ≤ ((n + 1 : ℕ) : ℝ) * (b - a) := hpower.2
      _ ≤ ((n + 1 : ℕ) : ℝ) * (C / ((n + 1 : ℕ) : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hgap hn.le
      _ = C / ((n + 1 : ℕ) : ℝ) := by
        field_simp
