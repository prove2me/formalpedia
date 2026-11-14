-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a71_original_gaussian_fullcell_clipped_spatial_endpoint_eq_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:57:12.337887+00:00
-- url     : https://prove2.me/submissions/5ffbabca-6f7f-4b8e-be31-be648b44b2f9

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- Before the true stop, a complete Gaussian physical mesh cell has exactly the original unclipped source and right-dividend Taylor endpoints. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (n m i : ℕ) (ρ : ℝ≥0)
    (hfull : let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i : ℝ≥0) * Δ + Δ ≤ ρ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) ρ
    v i = s ∧
      v (i + 1) = s + Δ ∧
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω =
        x + X.X (s + Δ) ω - rightLimit D s ω := by
  dsimp at hfull ⊢
  have hstart : (i : ℝ≥0) *
      ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) ≤ ρ :=
    le_trans (le_add_of_nonneg_right (zero_le)) hfull
  have hend : (((i + 1 : ℕ) : ℝ≥0) *
      ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) =
      (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) +
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) := by
    push_cast
    ring
  have hv0 : min ((i : ℝ≥0) *
      ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ρ =
      (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) :=
    min_eq_left hstart
  have hv1 : min (((i + 1 : ℕ) : ℝ≥0) *
      ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ρ =
      (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) +
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) := by
    rw [hend]
    exact min_eq_left hfull
  simp only [hv0, hv1, true_and, and_self]
