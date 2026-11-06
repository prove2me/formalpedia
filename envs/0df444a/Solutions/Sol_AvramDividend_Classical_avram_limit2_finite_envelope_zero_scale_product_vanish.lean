-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_finite_envelope_zero_scale_product_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:02:13.069593+00:00
-- url     : https://prove2.me/submissions/0ad35416-98ae-4e81-a07e-5f4971c59e0f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (scale : ℕ → ℝ≥0∞) (Envelope : Ω → ℝ≥0∞)
    (hFinite : (∫⁻ ω, Envelope ω ∂P) < ⊤)
    (hScale : Filter.Tendsto scale Filter.atTop (nhds (0 : ℝ≥0∞))) :
    Filter.Tendsto
      (fun n : ℕ => scale n * (∫⁻ ω, Envelope ω ∂P))
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  have hNeTop : (∫⁻ ω, Envelope ω ∂P) ≠ ⊤ := ne_top_of_lt hFinite
  simpa using (ENNReal.Tendsto.mul_const hScale (Or.inr hNeTop))
