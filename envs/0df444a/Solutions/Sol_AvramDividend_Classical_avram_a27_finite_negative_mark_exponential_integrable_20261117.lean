-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_finite_negative_mark_exponential_integrable_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:27:03.727721+00:00
-- url     : https://prove2.me/submissions/f09710b1-005a-4bb7-aa68-44df316f26c8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original finite negative mark measure integrates every nonnegative-tilt exponential. -/
theorem solution (ν : Measure ℝ)
    (hFinite : ν (Iio (0 : ℝ)) < ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    IntegrableOn (fun y : ℝ => Real.exp (θ * y))
      (Iio (0 : ℝ)) ν := by
  let μ : Measure ℝ := ν.restrict (Iio (0 : ℝ))
  haveI : IsFiniteMeasure μ := ⟨by simpa [μ] using hFinite⟩
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) μ :=
    integrable_const 1
  have hExpMeas : Measurable (fun y : ℝ => Real.exp (θ * y)) :=
    Real.measurable_exp.comp (measurable_const.mul measurable_id)
  have hExpBound :
      ∀ᵐ y ∂μ, ‖Real.exp (θ * y)‖ ≤ ‖(1 : ℝ)‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    have hmul : θ * y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hθ (le_of_lt hy)
    have hexp : Real.exp (θ * y) ≤ 1 :=
      (Real.exp_le_one_iff).2 hmul
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hexp
  have hExp : Integrable (fun y : ℝ => Real.exp (θ * y)) μ :=
    hone.mono hExpMeas.aestronglyMeasurable hExpBound
  exact hExp
