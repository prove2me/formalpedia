-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a343_nonnegative_ae_measurable_source_integrable_from_integrable_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:49:23.988566+00:00
-- url     : https://prove2.me/submissions/90495b0b-8404-450c-9c60-7d1b9782b0e5

import Mathlib.MeasureTheory.Function.L1Space.Integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F G : Ω → ℝ)
    (hFm : AEStronglyMeasurable F P)
    (hGI : Integrable G P)
    (hFpos : ∀ᵐ ω ∂P, 0 ≤ F ω)
    (hUpper : ∀ᵐ ω ∂P, F ω ≤ G ω) :
    Integrable F P := by
  apply Integrable.mono' hGI hFm
  filter_upwards [hFpos,hUpper] with ω hp hu
  have hg : 0 ≤ G ω := hp.trans hu
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg hp,abs_of_nonneg hg] using hu
