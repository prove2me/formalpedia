-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a552_gaussian_centered_Taylor_algebra_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:59:16.844248+00:00
-- url     : https://prove2.me/submissions/8ce78c78-2051-4b97-b995-d11e2031f392

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

theorem solution
    (a b z e K δ : ℝ)
    (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (ha : |a| ≤ K) (hb : |b| ≤ K)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    |e * (a * z + (b / 2) * (z ^ 2 - δ))| ≤
      (K * (2 + δ)) * (1 + z ^ 2) := by
  have hδ2 : |z ^ 2 - δ| ≤ z ^ 2 + δ := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg z]
  have hz : |z| ≤ 1 + z ^ 2 := by
    nlinarith [sq_nonneg (|z| - (1 / 2 : ℝ)), sq_abs z]
  have hmain :
      |a * z + (b / 2) * (z ^ 2 - δ)| ≤
        K * (2 + δ) * (1 + z ^ 2) := by
    calc
      |a * z + (b / 2) * (z ^ 2 - δ)| ≤
          |a * z| + |(b / 2) * (z ^ 2 - δ)| := abs_add_le _ _
      _ = |a| * |z| + (|b| / 2) * |z ^ 2 - δ| := by
        rw [abs_mul, abs_mul, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ K * |z| + (K / 2) * (z ^ 2 + δ) := by
        gcongr
      _ ≤ K * (2 + δ) * (1 + z ^ 2) := by
        have hKz := mul_le_mul_of_nonneg_left hz hK
        nlinarith [sq_nonneg z, mul_nonneg hK (sq_nonneg z)]
  calc
    |e * (a * z + (b / 2) * (z ^ 2 - δ))| =
        e * |a * z + (b / 2) * (z ^ 2 - δ)| := by
          rw [abs_mul, abs_of_nonneg he0]
    _ ≤ e * (K * (2 + δ) * (1 + z ^ 2)) :=
      mul_le_mul_of_nonneg_left hmain he0
    _ ≤ K * (2 + δ) * (1 + z ^ 2) := by
      have hp : 0 ≤ K * (2 + δ) * (1 + z ^ 2) := by positivity
      exact mul_le_of_le_one_left hp he1
