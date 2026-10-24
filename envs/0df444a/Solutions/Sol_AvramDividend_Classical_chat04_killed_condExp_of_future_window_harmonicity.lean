-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_condExp_of_future_window_harmonicity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:52:20.667493+00:00
-- url     : https://prove2.me/submissions/c4879f81-d124-4e24-943b-b71fca1927fa

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_standing_killed_discounted_condExp_time_split

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-! Future-window scale harmonicity implies the full killed conditional expectation identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u)
    (hFuture : P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
      (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω)) | 𝓕 s] =ᵐ[P]
      (fun ω => W (x + X.X s ω))) :
    P[({ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp (-(q * (u : ℝ))) * W (x + X.X u ω)) | 𝓕 s] =ᵐ[P]
      ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp (-(q * (s : ℝ))) * W (x + X.X s ω)) := by
  have hSplit :=
    chat04_standing_killed_discounted_condExp_time_split
      X hX τ hCover q hq W hW x s u hsu
  filter_upwards [hSplit, hFuture] with ω hsω hfω
  calc
    P[({ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp (-(q * (u : ℝ))) * W (x + X.X u ω)) | 𝓕 s] ω = ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp (-(q * (s : ℝ))) * P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
      (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω)) | 𝓕 s] ω) ω := hsω
    _ = ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp (-(q * (s : ℝ))) * W (x + X.X s ω)) ω := by
      by_cases h : ω ∈ ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω})
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, hfω]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
