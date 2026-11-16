-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB54s_original_physical_grid_masked_kink_source_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:57:52.650906+00:00
-- url     : https://prove2.me/submissions/18a70331-587a-47f4-862f-4ccbe2d728dc

import Theorems.Thm_AvramDividend_Classical_avram_gbB54n_nonnegative_weighted_caplinear_smooth_extension_grid_upper
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (a b α q x : ℝ) (hα : 1 ≤ α)
    (D : ℝ≥0 → Ω → ℝ) (n m : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let Y : ℕ → ℝ := fun i => x + X.X (s i) ω - rightLimit D (s i) ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let g : ℕ → ℝ := fun i => if a ≤ Y i then deriv w (Y i) else 1
    let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
    let U : ℝ → ℝ := fun z => if z ≤ b then w z else w b + α * (z - b)
    (∑ i ∈ Finset.range (m + 1), if s i < ρ ω then
      Real.exp (-(q * (s i : ℝ))) *
        (V (Y i + R i) - V (Y i) -
          (if Y i ≤ b then g i else 1) * R i)
      else 0) ≤
    (∑ i ∈ Finset.range (m + 1), if s i < ρ ω then
      Real.exp (-(q * (s i : ℝ))) *
        (U (Y i + R i) - U (Y i) -
          (if Y i ≤ b then g i else α) * R i)
      else 0) := by
  classical
  dsimp
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let Y : ℕ → ℝ := fun i => x + X.X (s i) ω - rightLimit D (s i) ω
  let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
  let G : ℕ → ℝ := fun i => if a ≤ Y i then deriv w (Y i) else 1
  let W : ℕ → ℝ := fun i =>
    if s i < ρ ω then Real.exp (-(q * (s i : ℝ))) else 0
  have hW : ∀ i ∈ Finset.range (m + 1), 0 ≤ W i := by
    intro i hi
    dsimp only [W]
    split_ifs <;> positivity
  have h := avram_gbB54n_nonnegative_weighted_caplinear_smooth_extension_grid_upper
    w b α hα (Finset.range (m + 1)) W Y (fun i => Y i + R i) G hW
  simpa [W, Y, R, G, s, Δ, ite_mul, mul_ite, add_sub_cancel_left] using h
