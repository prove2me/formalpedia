-- Prove2me | solution 1 for AvramDividend.Classical.avram_a67_nonpositive_jump_exponential_bounded_integrable_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:51:31.051513+00:00
-- url     : https://prove2.me/submissions/d6029283-b3d5-47e3-8579-51771d081556

import Mathlib.MeasureTheory.Integral.IntegrableOn
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

/-- A measurable nonpositive physical jump accumulator has a bounded integrable nonnegative-parameter exponential. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (J : Ω → ℝ) (θ : ℝ)
    (hMeas : Measurable J) (hθ : 0 ≤ θ)
    (hJ : ∀ᵐ ω ∂P, J ω ≤ 0) :
    Integrable (fun ω => Real.exp (θ * J ω)) P ∧
      (∀ᵐ ω ∂P,
        0 < Real.exp (θ * J ω) ∧
        Real.exp (θ * J ω) ≤ 1) := by
  have hMeasExp : Measurable (fun ω => Real.exp (θ * J ω)) := by
    fun_prop
  have hBounds : ∀ᵐ ω ∂P,
      0 < Real.exp (θ * J ω) ∧ Real.exp (θ * J ω) ≤ 1 := by
    filter_upwards [hJ] with ω hω
    constructor
    · exact Real.exp_pos _
    · apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonneg_of_nonpos hθ hω
  refine ⟨Integrable.of_bound hMeasExp.aestronglyMeasurable 1 ?_, hBounds⟩
  filter_upwards [hBounds] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos hω.1]
  exact hω.2
