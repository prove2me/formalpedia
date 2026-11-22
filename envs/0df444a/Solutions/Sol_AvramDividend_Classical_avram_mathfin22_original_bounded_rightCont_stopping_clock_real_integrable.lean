-- Prove2me | solution 1 for AvramDividend.Classical.avram_mathfin22_original_bounded_rightCont_stopping_clock_real_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T18:51:20.176131+00:00
-- url     : https://prove2.me/submissions/2bf75536-88e1-4685-a66a-fd634b4ebbb9

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

/-- A bounded original right-continuous stopping clock has finite real expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (hτbound : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0)) :
    Integrable (fun ω => ((τ ω).untopA : ℝ)) P := by
  have hm : Measurable (fun ω => ((τ ω).untopA : ℝ)) :=
    (Measurable.untopA hτ.measurable').coe_nnreal_real
  apply Integrable.of_bound hm.aestronglyMeasurable (T : ℝ)
  apply Filter.Eventually.of_forall
  intro ω
  have hFinite : τ ω ≠ ⊤ := by
    have hTtop : (T : WithTop ℝ≥0) < ⊤ := WithTop.coe_lt_top T
    exact ne_of_lt ((hτbound ω).trans_lt hTtop)
  have hρle : (τ ω).untopA ≤ T :=
    (WithTop.untopA_le_iff hFinite).2 (hτbound ω)
  rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
  exact NNReal.coe_le_coe.mpr hρle
