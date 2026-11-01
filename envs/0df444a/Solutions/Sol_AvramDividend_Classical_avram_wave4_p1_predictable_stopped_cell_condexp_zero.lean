-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_predictable_stopped_cell_condexp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:21:35.877496+00:00
-- url     : https://prove2.me/submissions/5ec27292-a97c-4a20-87b4-4285d8330cf4

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (mPast mFuture : MeasurableSpace Ω)
    (hPast : mPast ≤ mΩ)
    (hFuture : mFuture ≤ mΩ)
    [@SigmaFinite Ω mPast (P.trim hPast)]
    (H Z : Ω → ℝ)
    (hH : StronglyMeasurable[mPast] H)
    (hZ : StronglyMeasurable[mFuture] Z)
    (hProd : Integrable (H * Z) P)
    (hZi : Integrable Z P)
    (hIndep : Indep mFuture mPast P)
    (hCenter : ∫ ω, Z ω ∂P = 0) :
    P[H * Z | mPast] =ᵐ[P] (fun _ : Ω => (0 : ℝ)) := by
  have hfuture :
      P[Z | mPast] =ᵐ[P] (fun _ : Ω => (0 : ℝ)) := by
    simpa [hCenter] using
      (MeasureTheory.condExp_indep_eq hFuture hPast hZ hIndep)
  have hpull :
      P[H * Z | mPast] =ᵐ[P] H * P[Z | mPast] :=
    MeasureTheory.condExp_mul_of_stronglyMeasurable_left hH hProd hZi
  filter_upwards [hpull, hfuture] with ω hp hz
  simpa [hp, hz]
