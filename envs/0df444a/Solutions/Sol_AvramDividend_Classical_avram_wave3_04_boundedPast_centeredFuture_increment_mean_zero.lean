-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_boundedPast_centeredFuture_increment_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T13:36:36.72977+00:00
-- url     : https://prove2.me/submissions/465488cf-7bd4-4b88-b780-648a126af9f5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_general_future_increment_conditional_expectation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-- Bounded past-measurable coefficients integrate to zero against
centred original Levy increments, with product integrability derived. -/
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
    (∫ ω, H ω * φ (X.X t ω - X.X s ω) ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
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
  have hPull := condExp_mul_of_stronglyMeasurable_left
    (m := 𝓕 s) (μ := P) hH hIntProd hIntInc
  have hFuture :=
    chat04_general_future_increment_conditional_expectation
      X s t hst φ hφ hInt
  have hzero : P[(fun ω => H ω * φ (X.X t ω - X.X s ω)) | 𝓕 s] =ᵐ[P]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hPull, hFuture] with ω hp hf
    calc
      _ = (H * P[(fun ω => φ (X.X t ω - X.X s ω)) | 𝓕 s]) ω := hp
      _ = H ω * ∫ z, φ (X.X (t - s) z) ∂P := by
        simpa only [Pi.mul_apply] using
          congrArg (fun r : ℝ => H ω * r) hf
      _ = 0 := by simp [hmean]
  calc
    (∫ ω, H ω * φ (X.X t ω - X.X s ω) ∂P) =
        ∫ ω, P[(fun ω => H ω * φ (X.X t ω - X.X s ω)) | 𝓕 s] ω ∂P := by
      exact (integral_condExp (μ := P) (hm := 𝓕.le s)).symm
    _ = 0 := by
      rw [integral_congr_ae hzero]
      simp
