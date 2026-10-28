-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_leftshift_projective_martingale_early_events
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:35:54.787819+00:00
-- url     : https://prove2.me/submissions/8150d192-d3f6-4b4a-ab19-6d05c5d39e10

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_compensated_setIntegral_change
import Theorems.Thm_AvramDividend_Classical_chat01_levy_exponential_early_event_integral_eq
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ ε : ℝ) (hε : 0 ≤ ε) (hεθ : ε ≤ θ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A) :
    (∫ ω in A, Real.exp (-ε * X.X s ω -
        (s : ℝ) * (X.ψ (θ - ε) - X.ψ θ)) ∂(P.withDensity (fun ω : Ω =>
        ENNReal.ofReal
          (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ))))) =
    (∫ ω in A, Real.exp (-ε * X.X t ω -
        (t : ℝ) * (X.ψ (θ - ε) - X.ψ θ)) ∂(P.withDensity (fun ω : Ω =>
        ENNReal.ofReal
          (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))))) := by
  haveI := X.isProbability
  have hA' : MeasurableSet A := 𝓕.le s A hA
  rw [chat04_esscher_leftshift_compensated_setIntegral_change X s θ ε A hA',
    chat04_esscher_leftshift_compensated_setIntegral_change X t θ ε A hA']
  exact chat01_levy_exponential_early_event_integral_eq X (θ - ε) (by linarith) s t hst A hA
