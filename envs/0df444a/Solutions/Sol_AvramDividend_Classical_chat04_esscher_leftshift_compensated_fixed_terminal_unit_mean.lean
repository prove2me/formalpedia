-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_leftshift_compensated_fixed_terminal_unit_mean
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:29:53.270281+00:00
-- url     : https://prove2.me/submissions/67f1a16f-0fc9-44e1-9e19-a60e94980bd1

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_expectation_one
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_compensated_setIntegral_change
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_past_event_setIntegral_consistency
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_compensated_leftshift_reward_strongly_adapted
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ ε : ℝ) (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (hεθ : ε ≤ θ)
    (s T : ℝ≥0) (hsT : s ≤ T) :
    (∫ ω, Real.exp
      (-ε * X.X s ω -
        (s : ℝ) * (X.ψ (θ - ε) - X.ψ θ)) ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) = 1 := by
  have h1 := chat04_esscher_past_event_setIntegral_consistency X θ hθ s T hsT Set.univ
    MeasurableSet.univ _ (chat04_esscher_compensated_leftshift_reward_strongly_adapted X θ ε s)
  have h2 := chat04_esscher_leftshift_compensated_setIntegral_change X s θ ε Set.univ
    MeasurableSet.univ
  simp only [Measure.restrict_univ] at h1 h2
  rw [← h1, h2]
  exact levy_compensated_exponential_expectation_one X s (θ - ε) (by linarith)
