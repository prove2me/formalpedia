-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a540_ae_bounded_real_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:38:50.346408+00:00
-- url     : https://prove2.me/submissions/ed1f0402-3506-42f2-a0c3-3b1335ba9ba5

import Mathlib.MeasureTheory.Function.L1Space.Integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (f : Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hf : AEStronglyMeasurable f P)
    (hb : ∀ᵐ ω ∂P, |f ω| ≤ K)
    (hconst : Integrable (fun _ : Ω => K) P) :
    Integrable f P := by
  apply hconst.mono' hf
  filter_upwards [hb] with ω hω
  simpa [Real.norm_eq_abs, Real.norm_of_nonneg hK] using hω
