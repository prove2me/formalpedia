-- Prove2me | solution 2 for AvramDividend.Classical.chat04_esscher_leftshift_fixed_terminal_nat_grid_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:32:57.096324+00:00
-- url     : https://prove2.me/submissions/38a234f9-3e65-49cf-8587-ec77f04a9b8e

import Mathlib.Probability.Martingale.Basic
import Theorems.Thm_AvramDividend_Classical_fixed_terminal_real_time_martingale_discretizes_on_any_bounded_monotone_grid
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_compensated_leftshift_reward_strongly_adapted
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_compensated_fixed_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_fixed_terminal_martingale_early_events
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
  let Q : Measure Ω := P.withDensity (fun ω : Ω => ENNReal.ofReal
    (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
  let Z : ℝ≥0 → Ω → ℝ := fun r ω => Real.exp
    (-ε * X.X r ω - (r : ℝ) * (X.ψ (θ - ε) - X.ψ θ))
  haveI hprob : IsProbabilityMeasure Q := by
    dsimp [Q]
    simpa only [SpectrallyNegativeLevy.ψ] using
      chat04_esscher_weighted_finite_horizon_probability X T θ hθ
  have hadapt : ∀ r : ℝ≥0, StronglyMeasurable[𝓕 r] (Z r) :=
    chat04_esscher_compensated_leftshift_reward_strongly_adapted X θ ε
  have hint : ∀ n : ℕ, Integrable (Z (g n)) Q := by
    intro n
    simpa only [Z, Q] using
      chat04_esscher_leftshift_compensated_fixed_terminal_integrable
        X θ ε hθ hε hεθ (g n) T (hgT n)
  have hevents : ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      ∀ A : Set Ω, @MeasurableSet Ω (𝓕 s) A →
      (∫ ω in A, Z s ω ∂Q) = (∫ ω in A, Z t ω ∂Q) := by
    intro s t hst htT A hA
    simpa only [Z, Q] using
      chat04_esscher_leftshift_fixed_terminal_martingale_early_events
        X θ ε hθ hε hεθ s t T hst htT A hA
  simpa only [Z, Q] using
    fixed_terminal_real_time_martingale_discretizes_on_any_bounded_monotone_grid
      (𝓕 := 𝓕) T g hg hgT Q Z hadapt hint hevents
