-- Prove2me | solution 1 for AvramDividend.Classical.negative_exponential_residual_integral_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T23:06:16.550099+00:00
-- url     : https://prove2.me/submissions/e5b737f9-4b1f-4992-b0fa-58d9808e57e2

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory

theorem solution
    (ν : Measure ℝ) (hneg : ∀ᵐ y ∂ν, y < 0)
    (hA : Integrable (fun y : ℝ => |y|) ν) :
    Tendsto (fun n : ℕ =>
      ∫ y : ℝ, (1 - Real.exp (((n : ℝ) + 1) * y)) /
        ((n : ℝ) + 1) ∂ν) atTop (nhds (0 : ℝ)) := by
  have hmeas (n : ℕ) :
      AEStronglyMeasurable (fun y : ℝ =>
        (1 - Real.exp (((n : ℝ) + 1) * y)) / ((n : ℝ) + 1)) ν := by
    fun_prop
  have hdom (n : ℕ) : ∀ᵐ y ∂ν,
      ‖(1 - Real.exp (((n : ℝ) + 1) * y)) /
        ((n : ℝ) + 1)‖ ≤ |y| := by
    filter_upwards [hneg] with y hy
    have hθ : 0 < (n : ℝ) + 1 := by positivity
    have hz : ((n : ℝ) + 1) * y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hθ.le hy.le
    have hexp_le : Real.exp (((n : ℝ) + 1) * y) ≤ 1 :=
      Real.exp_le_one_iff.mpr hz
    have hnonneg : 0 ≤ (1 - Real.exp (((n : ℝ) + 1) * y)) /
        ((n : ℝ) + 1) :=
      div_nonneg (sub_nonneg.mpr hexp_le) hθ.le
    have hupper : (1 - Real.exp (((n : ℝ) + 1) * y)) /
        ((n : ℝ) + 1) ≤ |y| := by
      rw [abs_of_neg hy]
      apply (div_le_iff₀ hθ).2
      linarith [Real.add_one_le_exp (((n : ℝ) + 1) * y)]
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hupper
  have hpt : ∀ᵐ y ∂ν,
      Tendsto (fun n : ℕ =>
        (1 - Real.exp (((n : ℝ) + 1) * y)) / ((n : ℝ) + 1))
        atTop (nhds (0 : ℝ)) := by
    filter_upwards [hneg] with y hy
    have hrecip : Tendsto (fun n : ℕ =>
        (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hb (n : ℕ) :
        0 ≤ (1 - Real.exp (((n : ℝ) + 1) * y)) / ((n : ℝ) + 1) ∧
        (1 - Real.exp (((n : ℝ) + 1) * y)) / ((n : ℝ) + 1) ≤
        (1 : ℝ) / ((n : ℝ) + 1) := by
      have hθ : 0 < (n : ℝ) + 1 := by positivity
      have hz : ((n : ℝ) + 1) * y ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hθ.le hy.le
      have hexp_le : Real.exp (((n : ℝ) + 1) * y) ≤ 1 :=
        Real.exp_le_one_iff.mpr hz
      have hexp_pos : 0 ≤ Real.exp (((n : ℝ) + 1) * y) :=
        (Real.exp_pos _).le
      constructor
      · exact div_nonneg (sub_nonneg.mpr hexp_le) hθ.le
      · exact div_le_div_of_nonneg_right (by linarith) hθ.le
    exact squeeze_zero (fun n => (hb n).1) (fun n => (hb n).2) hrecip
  have hlim := tendsto_integral_of_dominated_convergence
    (fun y : ℝ => |y|) hmeas hA hdom hpt
  simpa using hlim
