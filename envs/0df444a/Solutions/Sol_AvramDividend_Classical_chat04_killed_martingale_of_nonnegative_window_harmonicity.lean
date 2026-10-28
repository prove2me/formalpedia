-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_martingale_of_nonnegative_window_harmonicity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:51:14.755057+00:00
-- url     : https://prove2.me/submissions/e5fca38e-923d-4183-9337-c87309e1c9b5

import Mathlib.Data.Nat.Pairing
import Mathlib.Probability.Martingale.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage
import Theorems.Thm_AvramDividend_Classical_chat04_future_window_harmonicity_of_nonnegative_state
import Theorems.Thm_AvramDividend_Classical_chat04_killed_martingale_of_future_window_harmonicity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

/-- Positive-reserve future-window q-harmonicity implies the full killed martingale,
using the canonical rational-time schedule and the scale function's negative support. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ)
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
  let τ : ℕ → ℝ≥0 := fun j =>
    ((Nat.unpair j).2 : ℝ≥0) *
      ((((Nat.unpair j).1 + 1 : ℕ) : ℝ≥0)⁻¹)
  have hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹ := by
    intro n hn k
    exact chat04_nat_pairing_rational_grid_coverage n k hn
  apply chat04_killed_martingale_of_future_window_harmonicity
    X hX τ hCover q hq W hW x
  intro s u hsu
  exact chat04_future_window_harmonicity_of_nonnegative_state
    X hX q hq W hW x s u hsu (fun y hy => hW.1 y hy)
    (hPositive s u hsu)
