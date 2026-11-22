-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_finite_grid_stopped_martingale_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T12:54:39.362812+00:00
-- url     : https://prove2.me/submissions/d527f58b-d7db-4c67-b968-e8dfbd3ead17

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/-
Adapted from dufeteller/lean-lsv, LSV/LocalizedOptionalExpectation.lean,
continuous_martingale_optional_expectation finite stopping-grid step,
commit a5f604de2e1ae431de4cbecde23e5694a12ba719, upstream CC BY 4.0.
The theorem uses a real, countable-range stopped martingale in the original
nonnegative-time filtration; boundedness is explicit, with no extra envelope.
-/

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M ℱ μ)
    (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime ℱ τ)
    (hτbound : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτcount : (Set.range τ).Countable) :
    Integrable (stoppedValue M τ) μ ∧
      (∫ ω, stoppedValue M τ ω ∂μ) = ∫ ω, M T ω ∂μ := by
  have hae := hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
    hτ hτbound hτcount
  have hi : Integrable (stoppedValue M τ) μ :=
    (integrable_condExp (m := hτ.measurableSpace)).congr hae.symm
  refine ⟨hi, ?_⟩
  have hh := integral_congr_ae hae
  rw [integral_condExp hτ.measurableSpace_le] at hh
  exact hh

