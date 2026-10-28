-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_leftshift_fixed_terminal_nat_grid_martingale
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:32:43.266292+00:00
-- url     : https://prove2.me/submissions/8985d853-b5d6-42ec-b272-25d9553c0a20

import Mathlib.Probability.Martingale.Basic
import Theorems.Thm_AvramDividend_Classical_fixed_terminal_real_time_martingale_discretizes_on_any_bounded_monotone_grid
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_compensated_leftshift_reward_strongly_adapted
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_compensated_fixed_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_fixed_terminal_martingale_early_events
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ ε : ℝ) (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (hεθ : ε ≤ θ)
    (T : ℝ≥0) (g : ℕ → ℝ≥0) (hg : Monotone g)
    (hgT : ∀ n : ℕ, g n ≤ T) :
    ∃ 𝓖 : Filtration ℕ mΩ,
      (∀ n : ℕ, 𝓖 n = 𝓕 (g n)) ∧
      Martingale
        (fun n ω => Real.exp
          (-ε * X.X (g n) ω -
            (g n : ℝ) * (X.ψ (θ - ε) - X.ψ θ)))
        𝓖
        (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) := by
  haveI : IsProbabilityMeasure (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) :=
    chat04_esscher_weighted_finite_horizon_probability X T θ hθ
  exact fixed_terminal_real_time_martingale_discretizes_on_any_bounded_monotone_grid T g hg hgT _
    (fun t ω => Real.exp (-ε * X.X t ω - (t : ℝ) * (X.ψ (θ - ε) - X.ψ θ)))
    (chat04_esscher_compensated_leftshift_reward_strongly_adapted X θ ε)
    (fun n => chat04_esscher_leftshift_compensated_fixed_terminal_integrable X θ ε hθ hε hεθ _ T (hgT n))
    (fun s t hst htT A hA =>
      chat04_esscher_leftshift_fixed_terminal_martingale_early_events X θ ε hθ hε hεθ s t T hst htT A hA)
