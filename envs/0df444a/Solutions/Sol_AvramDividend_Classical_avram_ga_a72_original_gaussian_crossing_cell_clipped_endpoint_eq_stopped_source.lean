-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a72_original_gaussian_crossing_cell_clipped_endpoint_eq_stopped_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:50:20.743961+00:00
-- url     : https://prove2.me/submissions/b3227fff-bc20-491a-9d51-2f315ebb6333

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- The unique true stopping-straddling Gaussian physical cell is clipped at the actual stop, with original right-dividend state. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (n m i : ℕ) (ρ : ℝ≥0)
    (hstart : let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i : ℝ≥0) * Δ < ρ)
    (hend : let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ρ ≤ (i : ℝ≥0) * Δ + Δ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) ρ
    v i = s ∧ v (i + 1) = ρ ∧
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω =
        x + X.X ρ ω - rightLimit D s ω := by
  dsimp at hstart hend ⊢
  have hnext : (((i + 1 : ℕ) : ℝ≥0) *
      ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) =
      (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) +
        ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) := by
    push_cast
    ring
  have hv0 : min ((i : ℝ≥0) *
      ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ρ =
      (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) :=
    min_eq_left hstart.le
  have hv1 : min (((i + 1 : ℕ) : ℝ≥0) *
      ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ρ = ρ := by
    rw [hnext]
    exact min_eq_right hend
  simp only [hv0, hv1, true_and, and_self]
