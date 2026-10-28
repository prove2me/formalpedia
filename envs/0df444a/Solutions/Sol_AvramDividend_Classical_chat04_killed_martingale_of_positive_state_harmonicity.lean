-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_martingale_of_positive_state_harmonicity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:41:39.921493+00:00
-- url     : https://prove2.me/submissions/8c619b39-25e0-4c58-806e-786ae2d08f95

import Mathlib.Probability.Martingale.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_future_window_harmonicity_of_nonnegative_state
import Theorems.Thm_AvramDividend_Classical_chat04_killed_martingale_of_future_window_harmonicity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

/-! A nonnegative-state future-window q-harmonicity identity suffices for the killed martingale. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hWneg : ∀ y : ℝ, y < 0 → W y = 0)
    (hPositive : ∀ s u : ℝ≥0, s ≤ u →
      ({ω | 0 ≤ x + X.X s ω}).indicator
        (P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
          0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
         (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
           W (x + X.X u ω)) | 𝓕 s]) =ᵐ[P]
      ({ω | 0 ≤ x + X.X s ω}).indicator
        (fun ω => W (x + X.X s ω))) :
    Martingale
      (fun t ω =>
        ({ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}).indicator
          (fun ω => Real.exp (-(q * (t : ℝ))) *
            W (x + X.X t ω)) ω) 𝓕 P := by
  apply chat04_killed_martingale_of_future_window_harmonicity
    X hX τ hCover q hq W hW x
  intro s u hsu
  exact chat04_future_window_harmonicity_of_nonnegative_state
    X hX q hq W hW x s u hsu hWneg (hPositive s u hsu)
