-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB294b_probability_fibre_integral_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:20:58.280002+00:00
-- url     : https://prove2.me/submissions/4358165f-fa08-4c7c-923a-427f2bf5aebc

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Original source-fibre probability bounds transfer to a product-time integral. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Set (Ω × ℝ)) (hS : MeasurableSet S)
    (g : ℝ → ℝ≥0∞)
    (hFibre : ∀ t : ℝ, P ((fun ω : Ω => (ω, t)) ⁻¹' S) ≤ g t) :
    (P.prod volume) S ≤ ∫⁻ t : ℝ, g t ∂volume := by
  rw [Measure.prod_apply_symm hS]
  exact lintegral_mono hFibre
