-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_leftshift_fixed_terminal_martingale_early_events
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:19:33.946832+00:00
-- url     : https://prove2.me/submissions/54f14de8-cc37-47bf-a93f-6693b1827163

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_projective_martingale_early_events_fixed_terminal_law
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_projective_martingale_early_events
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_compensated_leftshift_reward_strongly_adapted
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
    (s t T : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A) :
    (∫ ω in A, Real.exp
       (-ε * X.X s ω -
         (s : ℝ) * (X.ψ (θ - ε) - X.ψ θ)) ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) =
    (∫ ω in A, Real.exp
       (-ε * X.X t ω -
         (t : ℝ) * (X.ψ (θ - ε) - X.ψ θ)) ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) := by
  let Q : ℝ≥0 → Measure Ω := fun r =>
    P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X r ω - (r : ℝ) * X.ψ θ)))
  let Z : ℝ≥0 → Ω → ℝ := fun r ω =>
    Real.exp (-ε * X.X r ω -
      (r : ℝ) * (X.ψ (θ - ε) - X.ψ θ))
  have hQ : ∀ u v : ℝ≥0, u ≤ v →
      ∀ B : Set Ω, @MeasurableSet Ω (𝓕 u) B → Q u B = Q v B := by
    intro u v huv B hB
    simpa only [Q, SpectrallyNegativeLevy.ψ] using
      chat04_esscher_finite_horizon_laws_consistent_on_past_events
        X θ hθ u v huv B hB
  have hZ : ∀ u v : ℝ≥0, u ≤ v →
      ∀ B : Set Ω, @MeasurableSet Ω (𝓕 u) B →
      (∫ ω in B, Z u ω ∂Q u) =
      (∫ ω in B, Z v ω ∂Q v) := by
    intro u v huv B hB
    simpa only [Z, Q] using
      chat04_esscher_leftshift_projective_martingale_early_events
        X θ ε hε hεθ u v huv B hB
  have hadapt : ∀ r : ℝ≥0, StronglyMeasurable[𝓕 r] (Z r) :=
    chat04_esscher_compensated_leftshift_reward_strongly_adapted
      X θ ε
  simpa only [Z, Q] using
    projective_martingale_early_events_fixed_terminal_law
      Q Z hQ hZ hadapt s t T hst htT A hA
