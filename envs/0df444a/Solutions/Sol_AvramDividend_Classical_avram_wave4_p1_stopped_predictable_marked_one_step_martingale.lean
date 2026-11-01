-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_stopped_predictable_marked_one_step_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:21:04.757753+00:00
-- url     : https://prove2.me/submissions/8c62953b-8fe7-44f1-9b3f-33fd19c405d9

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
    (G H Z : Ω → ℝ)
    (hG : StronglyMeasurable[mPast] G)
    (hGi : Integrable G P)
    (hH : StronglyMeasurable[mPast] H)
    (hZ : StronglyMeasurable[mFuture] Z)
    (hProd : Integrable (H * Z) P)
    (hZi : Integrable Z P)
    (hIndep : Indep mFuture mPast P)
    (hCenter : ∫ ω, Z ω ∂P = 0) :
    P[G + H * Z | mPast] =ᵐ[P] G := by
  have hfuture :
      P[Z | mPast] =ᵐ[P] (fun _ : Ω => (0 : ℝ)) := by
    simpa [hCenter] using
      (MeasureTheory.condExp_indep_eq hFuture hPast hZ hIndep)
  have hpull :
      P[H * Z | mPast] =ᵐ[P] H * P[Z | mPast] :=
    MeasureTheory.condExp_mul_of_stronglyMeasurable_left hH hProd hZi
  have hGcond : P[G | mPast] = G :=
    MeasureTheory.condExp_of_stronglyMeasurable hPast hG hGi
  have hsum :
      P[G + H * Z | mPast] =ᵐ[P]
        P[G | mPast] + P[H * Z | mPast] :=
    MeasureTheory.condExp_add hGi hProd mPast
  filter_upwards [hsum, hpull, hfuture] with ω hs hp hz
  simpa [hs, hp, hz, hGcond]
