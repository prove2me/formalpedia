-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_closed_horizon_survival_condExp_future_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:21:26.581227+00:00
-- url     : https://prove2.me/submissions/3ec89f09-10d9-4cf3-ad14-4db9a50b3d51

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_closed_horizon_survival_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_past_event_scale_condExp
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
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
  let A : Set Ω := {ω | ∀ t : ℝ≥0, t ≤ T →
    ¬ (X.X t ω < lower ∨ upper < X.X t ω)}
  have hA : MeasurableSet[𝓕 T] A :=
    chat04_closed_horizon_survival_filtration_measurable
      X τ hCover lower upper T
  exact chat04_unbounded_past_event_scale_condExp
    X q hq W hW hnbv T u hTu x A hA
