-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_martingale_of_future_window_harmonicity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:57:22.086687+00:00
-- url     : https://prove2.me/submissions/fe8910eb-8505-4e4b-babb-101f06f2b796

import Mathlib.Probability.Martingale.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_killed_martingale_of_condExp_identity
import Theorems.Thm_AvramDividend_Classical_chat04_killed_condExp_of_future_window_harmonicity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-! Future-window harmonicity is sufficient for the full killed q-scale martingale. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ)
    (hFuture : ∀ s u : ℝ≥0, s ≤ u →
      P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
          0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
        (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
          W (x + X.X u ω)) | 𝓕 s] =ᵐ[P] (fun ω => W (x + X.X s ω))) :
    Martingale (fun t ω =>
      ({ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω) 𝓕 P := by
  apply chat04_killed_martingale_of_condExp_identity
    X hX q hq W hW x (fun t ω =>
      ({ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω) rfl
  intro s u hsu
  exact chat04_killed_condExp_of_future_window_harmonicity
    X hX τ hCover q hq W hW x s u hsu (hFuture s u hsu)
