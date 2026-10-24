-- Prove2me | solution 1 for AvramDividend.Classical.chat04_standing_killed_discounted_condExp_time_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:09:36.945709+00:00
-- url     : https://prove2.me/submissions/164c5dcb-7416-4a20-b24c-877c93dbb00e

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_killed_discounted_condExp_time_split
import Theorems.Thm_AvramDividend_Classical_chat04_standing_future_window_killed_scale_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-! Time-splitting of the killed discounted q-scale conditional
expectation without an additional integrability assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    P[({ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (u : ℝ))) * W (x + X.X u ω)) | 𝓕 s] =ᵐ[P]
      ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (s : ℝ))) *
          P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
            0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
              (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
                W (x + X.X u ω)) | 𝓕 s] ω) := by
  have hInt : Integrable
      (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
        (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
          W (x + X.X u ω))) P :=
    chat04_standing_future_window_killed_scale_integrable
      X hX q hq W hW x s u hsu
  exact chat04_killed_discounted_condExp_time_split
    X τ hCover q W x s u hsu hInt
