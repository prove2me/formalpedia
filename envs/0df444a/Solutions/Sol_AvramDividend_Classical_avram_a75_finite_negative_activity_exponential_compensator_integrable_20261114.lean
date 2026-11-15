-- Prove2me | solution 1 for AvramDividend.Classical.avram_a75_finite_negative_activity_exponential_compensator_integrable_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:18:46.471614+00:00
-- url     : https://prove2.me/submissions/77e40063-2690-46fa-9986-b1b1e7cc505f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (ν : Measure ℝ) (hFinite : ν (Iio (0 : ℝ)) < ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    IntegrableOn (fun y : ℝ => Real.exp (θ * y) - 1)
      (Iio (0 : ℝ)) ν ∧
    IntegrableOn
      (fun y : ℝ => y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y)
      (Iio (0 : ℝ)) ν := by
  let μ : Measure ℝ := ν.restrict (Iio (0 : ℝ))
  haveI : IsFiniteMeasure μ := ⟨by simpa [μ] using hFinite⟩
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) μ := integrable_const 1
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
  have hExpMinus : Integrable (fun y : ℝ => Real.exp (θ * y) - 1) μ :=
    hExp.sub hone
  have hCompMeas :
      Measurable (fun y : ℝ =>
        y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y) :=
    measurable_id.mul (measurable_const.indicator measurableSet_Ioo)
  have hCompBound :
      ∀ᵐ y ∂μ,
        ‖y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y‖ ≤
          ‖(1 : ℝ)‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    by_cases hB : y ∈ Ioo (-1 : ℝ) 1
    · have habs : |y| ≤ (1 : ℝ) :=
        (abs_le).2 ⟨le_of_lt hB.1, le_of_lt hB.2⟩
      simpa [Set.indicator, hB, Real.norm_eq_abs] using habs
    · simp [Set.indicator, hB]
  have hComp : Integrable
      (fun y : ℝ => y * (Ioo (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y) μ :=
    hone.mono hCompMeas.aestronglyMeasurable hCompBound
  exact ⟨hExpMinus, hComp⟩
