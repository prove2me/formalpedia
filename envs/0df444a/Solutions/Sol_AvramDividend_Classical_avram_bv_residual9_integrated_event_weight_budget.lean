-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_integrated_event_weight_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:09:37.247289+00:00
-- url     : https://prove2.me/submissions/898530b0-c2ec-44d8-8867-eb782522749e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

/-- Integrating a pathwise nonpositive budget bound weighted by an event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (A B : Ω → ℝ) (κ : ℝ)
    (hA : Integrable A P) (hB : Integrable B P)
    (hbound : ∀ᵐ ω ∂P, B ω ≤ -κ * A ω) :
    (∫ ω, B ω ∂P) ≤ -κ * (∫ ω, A ω ∂P) := by
  have hconst : Integrable (fun ω => -κ * A ω) P := hA.const_mul (-κ)
  calc
    (∫ ω, B ω ∂P) ≤ ∫ ω, -κ * A ω ∂P :=
      integral_mono_ae hB hconst hbound
    _ = -κ * (∫ ω, A ω ∂P) := by rw [integral_const_mul]
