-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_boundedPast_centeredFuture_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T17:42:07.878851+00:00
-- url     : https://prove2.me/submissions/294518df-c193-4131-b39b-b9af34f3d7ed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_pastCoefficient_futureIncrement_condExp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-- A bounded observation in the genuine past has zero conditional mean
when multiplied by a centred integrable original future Lévy payoff.
Product integrability is derived, not assumed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (φ : ℝ → ℝ) (hφ : Measurable φ)
    (H : Ω → ℝ) (hH : StronglyMeasurable[𝓕 s] H)
    (K : ℝ) (hBound : ∀ ω, ‖H ω‖ ≤ K)
    (hInt : Integrable (fun ω => φ (X.X (t - s) ω)) P)
    (hmean : (∫ ω, φ (X.X (t - s) ω) ∂P) = 0) :
    P[(fun ω => H ω * φ (X.X t ω - X.X s ω)) | 𝓕 s] =ᵐ[P]
      (fun _ => (0 : ℝ)) := by
  have hIdent : IdentDistrib
      (fun ω => φ (X.X t ω - X.X s ω))
      (fun ω => φ (X.X (t - s) ω)) P P := by
    simpa only [Function.comp_def] using
      (X.stationaryIncrements s t hst).comp hφ
  have hIntInc : Integrable
      (fun ω => φ (X.X t ω - X.X s ω)) P :=
    hIdent.integrable_iff.mpr hInt
  have hHfull : StronglyMeasurable H := hH.mono (𝓕.le s)
  have hIntProd : Integrable
      (fun ω => H ω * φ (X.X t ω - X.X s ω)) P := by
    exact hIntInc.bdd_mul hHfull.aestronglyMeasurable
      (Filter.Eventually.of_forall hBound)
  have hCE :=
    avram_wave3_04_pastCoefficient_futureIncrement_condExp
      X s t hst φ hφ H hH hInt hIntInc hIntProd
  filter_upwards [hCE] with ω hω
  simpa only [hmean, mul_zero] using hω
