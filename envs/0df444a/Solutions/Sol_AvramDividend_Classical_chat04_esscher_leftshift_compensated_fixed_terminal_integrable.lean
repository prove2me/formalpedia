-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_leftshift_compensated_fixed_terminal_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:26:02.716715+00:00
-- url     : https://prove2.me/submissions/da069f22-6c27-483d-94c3-9fc41ab4734a

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Probability.Process.Filtration
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_integrable_iff_of_ambient_measures_agree_on_subsigma
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_negative_exp_integrable
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
    Integrable (fun ω : Ω => Real.exp
      (-ε * X.X s ω -
        (s : ℝ) * (X.ψ (θ - ε) - X.ψ θ)))
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) := by
  have hs := chat04_esscher_finite_negative_exp_integrable X s θ ε hθ hε hεθ
  have hs' : Integrable (fun ω : Ω => Real.exp
      (-ε * X.X s ω - (s : ℝ) * (X.ψ (θ - ε) - X.ψ θ)))
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)))) := by
    have := hs.mul_const (Real.exp (-((s : ℝ) * (X.ψ (θ - ε) - X.ψ θ))))
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    rw [← Real.exp_add]; ring_nf
  refine (integrable_iff_of_ambient_measures_agree_on_subsigma (𝓕.le s) _ _ ?_ _
    (chat04_esscher_compensated_leftshift_reward_strongly_adapted X θ ε s)).1 hs'
  intro B hB
  exact chat04_esscher_finite_horizon_laws_consistent_on_past_events X θ hθ s T hsT B hB
