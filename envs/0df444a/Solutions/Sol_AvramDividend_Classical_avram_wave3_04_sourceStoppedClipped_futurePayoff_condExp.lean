-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_sourceStoppedClipped_futurePayoff_condExp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T17:31:23.043541+00:00
-- url     : https://prove2.me/submissions/52d7fff2-e878-4288-81d3-7aaa5f2812b1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_stopped_discounted_deriv_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_pastCoefficient_futureIncrement_condExp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Genuine source-Lévy future-payoff conditional expectation with the
same-path stopped, discounted, clipped derivative of the controlled reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (T s t : ℝ≥0) (hst : s ≤ t)
    (φ : ℝ → ℝ) (hφ : Measurable φ)
    (hInt : Integrable (fun ω => φ (X.X (t - s) ω)) P) :
    P[(fun ω =>
      max (-K) (min K
        (if s ≤ T then
          (Real.exp (-(q * (s : ℝ))) *
            deriv w (Function.leftLim
              (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) s)) *
          (if (s : ℝ≥0∞) ≤ ruinTime X x D ω then
            (1 : ℝ) else 0)
        else 0)) *
      φ (X.X t ω - X.X s ω)) | 𝓕.rightCont s] =ᵐ[P]
    (fun ω =>
      max (-K) (min K
        (if s ≤ T then
          (Real.exp (-(q * (s : ℝ))) *
            deriv w (Function.leftLim
              (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) s)) *
          (if (s : ℝ≥0∞) ≤ ruinTime X x D ω then
            (1 : ℝ) else 0)
        else 0)) *
      ∫ z, φ (X.X (t - s) z) ∂P) := by
  let Z : ℝ≥0 → Ω → ℝ := fun u ω =>
    if u ≤ T then
      (Real.exp (-(q * (u : ℝ))) *
        deriv w (Function.leftLim
          (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u)) *
      (if (u : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
    else 0
  have hZ : IsStronglyPredictable 𝓕.rightCont Z :=
    avram_wave3_04_source_stopped_discounted_deriv_predictable
      X x D hD w q T
  have hClip := avram_wave3_04_clipped_stronglyPredictable_bounded
    Z hZ K hK
  have hCoeff : StronglyMeasurable[𝓕.rightCont s]
      (fun ω => max (-K) (min K (Z s ω))) :=
    hClip.1.stronglyAdapted s
  obtain ⟨Y, hYX, _, _, _⟩ := levy_rightCont_process X
  have hIdent : IdentDistrib
      (fun ω => φ (Y.X t ω - Y.X s ω))
      (fun ω => φ (Y.X (t - s) ω)) P P := by
    simpa only [Function.comp_def] using
      (Y.stationaryIncrements s t hst).comp hφ
  have hIntY : Integrable (fun ω => φ (Y.X (t - s) ω)) P := by
    simpa only [hYX] using hInt
  have hInc : Integrable (fun ω => φ (Y.X t ω - Y.X s ω)) P :=
    hIdent.integrable_iff.mpr hIntY
  have hProd : Integrable
      (fun ω => max (-K) (min K (Z s ω)) *
        φ (Y.X t ω - Y.X s ω)) P :=
    hInc.bdd_mul
      (hCoeff.mono ((𝓕.rightCont).le s)).aestronglyMeasurable
      (Filter.Eventually.of_forall (hClip.2 s))
  have hEq := avram_wave3_04_pastCoefficient_futureIncrement_condExp
    Y s t hst φ hφ
    (fun ω => max (-K) (min K (Z s ω)))
    hCoeff hIntY hInc hProd
  simpa only [hYX] using hEq
