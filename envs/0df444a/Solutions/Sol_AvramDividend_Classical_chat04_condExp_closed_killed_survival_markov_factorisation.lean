-- Prove2me | solution 1 for AvramDividend.Classical.chat04_condExp_closed_killed_survival_markov_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T22:49:32.956998+00:00
-- url     : https://prove2.me/submissions/c645508d-d858-419f-967f-c8b8b6a83d62

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_closed_horizon_survival_pathwise_markov_split
import Theorems.Thm_AvramDividend_Classical_chat04_closed_survival_conditioning_any_integrable_payoff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
The full conditional killed-survival factorisation:
 E[1_{survival [0,u]} f | F_s]
   = 1_{survival [0,s]} E[1_{future survival [s,u]} f | F_s].
This is exact for path-dependent real f, assuming integrability of the
future-killed payoff, and avoids claiming unproved future-path Markovianity.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower upper : ℝ) (s u : ℝ≥0) (hsu : s ≤ u)
    (f : Ω → ℝ)
    (hFutureInt : Integrable
      (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        ¬ (X.X s ω + (X.X v ω - X.X s ω) < lower ∨
          upper < X.X s ω + (X.X v ω - X.X s ω))}).indicator f) P) :
    P[({ω | ∀ v : ℝ≥0, v ≤ u →
        ¬ (X.X v ω < lower ∨ upper < X.X v ω)}).indicator f | 𝓕 s] =ᵐ[P]
      ({ω | ∀ v : ℝ≥0, v ≤ s →
        ¬ (X.X v ω < lower ∨ upper < X.X v ω)}).indicator
        (P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        ¬ (X.X s ω + (X.X v ω - X.X s ω) < lower ∨
          upper < X.X s ω + (X.X v ω - X.X s ω))}).indicator f | 𝓕 s]) := by
  let A : Set Ω := {ω | ∀ v : ℝ≥0, v ≤ s →
        ¬ (X.X v ω < lower ∨ upper < X.X v ω)}
  let B : Set Ω := {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        ¬ (X.X s ω + (X.X v ω - X.X s ω) < lower ∨
          upper < X.X s ω + (X.X v ω - X.X s ω))}
  let D : Set Ω := {ω | ∀ v : ℝ≥0, v ≤ u →
        ¬ (X.X v ω < lower ∨ upper < X.X v ω)}
  have hSplit : D = A ∩ B := by
    dsimp [D, A, B]
    simpa only [zero_add] using
      (AvramDividend.Classical.chat04_closed_horizon_survival_pathwise_markov_split
        X s u hsu (0 : ℝ) lower upper)
  have hIndicator : D.indicator f = A.indicator (B.indicator f) := by
    funext ω
    rw [hSplit]
    by_cases ha : ω ∈ A
    · by_cases hb : ω ∈ B
      · simp [Set.indicator, ha, hb]
      · simp [Set.indicator, ha, hb]
    · simp [Set.indicator, ha]
  have hCond :
      P[A.indicator (B.indicator f) | 𝓕 s] =ᵐ[P]
        A.indicator (P[B.indicator f | 𝓕 s]) := by
    exact
      AvramDividend.Classical.chat04_closed_survival_conditioning_any_integrable_payoff
        X τ hCover lower upper s (B.indicator f) hFutureInt
  change P[D.indicator f | 𝓕 s] =ᵐ[P]
    A.indicator (P[B.indicator f | 𝓕 s])
  rw [hIndicator]
  exact hCond
