-- Prove2me | solution 1 for AvramDividend.Classical.chat04_closed_horizon_survival_condExp_future_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T21:37:23.718348+00:00
-- url     : https://prove2.me/submissions/da565016-7827-4429-ae65-75c215d512e0

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_closed_horizon_survival_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_standing_past_event_scale_condExp
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Conditional Markov expectation of the next scale payoff on full
CONTINUOUS-time survival through the closed horizon [0,T]. The historical
survival event is F_T-measurable, and Standing ensures scale integrability.
No future killed harmonicity or no-creeping assumption is used.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower upper : ℝ)
    (T u : ℝ≥0) (hTu : T ≤ u) (x : ℝ) :
    P[({ω | ∀ t : ℝ≥0, t ≤ T →
       ¬ (X.X t ω < lower ∨ upper < X.X t ω)}).indicator
        (fun ω => W (x + (X.X u ω - X.X T ω))) | 𝓕 T] =ᵐ[P]
      ({ω | ∀ t : ℝ≥0, t ≤ T →
       ¬ (X.X t ω < lower ∨ upper < X.X t ω)}).indicator
        (fun _ => ∫ ω, W (x + X.X (u - T) ω) ∂P) := by
  let A : Set Ω :=
    {ω | ∀ t : ℝ≥0, t ≤ T →
      ¬ (X.X t ω < lower ∨ upper < X.X t ω)}
  have hA : MeasurableSet[𝓕 T] A :=
    AvramDividend.Classical.chat04_closed_horizon_survival_filtration_measurable
      X τ hCover lower upper T
  exact AvramDividend.Classical.chat04_standing_past_event_scale_condExp
    X hX q hq W hW T u hTu x A hA
