-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger74_measurable_original_clipped_NNReal_clock_to_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:57:37.287955+00:00
-- url     : https://prove2.me/submissions/bd5b991f-7762-4292-9688-568667067a36

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

/-- A measurable finite nonnegative clock has a measurable clipped
    real-valued endpoint; the coercion preserves pointwise minima. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ρ : Ω → ℝ≥0)
    (hρ : Measurable (fun ω => (ρ ω : WithTop ℝ≥0)))
    (a : ℝ≥0) :
    Measurable (fun ω => ((min a (ρ ω) : ℝ≥0) : ℝ)) := by
  have hρnn : Measurable ρ :=
    measurable_coe_nnreal_ennreal_iff.mp hρ
  have hρreal : Measurable (fun ω => (ρ ω : ℝ)) :=
    hρnn.coe_nnreal_real
  have hmin : Measurable (fun ω => min (a : ℝ) (ρ ω : ℝ)) :=
    measurable_const.min hρreal
  simpa only [NNReal.coe_min] using hmin
