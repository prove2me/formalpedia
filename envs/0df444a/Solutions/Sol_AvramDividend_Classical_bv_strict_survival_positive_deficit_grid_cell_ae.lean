-- Prove2me | solution 1 for AvramDividend.Classical.bv_strict_survival_positive_deficit_grid_cell_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:45:22.053072+00:00
-- url     : https://prove2.me/submissions/9acf6078-97b4-492f-9a85-6a3866d6024a

import Theorems.Thm_AvramDividend_Classical_bv_strict_zero_ruin_deficit_increment_band_ae
import Theorems.Thm_AvramDividend_Classical_positive_grid_deficit_has_small_positive_increment
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Strict survival bounds each compensated Lévy grid increment.
    Positive total deficit forces a small positive increment on some cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (N : ℕ) (ts : ℕ → ℝ≥0) (b : ℝ)
    (hStep : ∀ k : ℕ, k < N → ts k ≤ ts (k + 1))
    (hWithin : ∀ k : ℕ, k < N → ts (k + 1) ≤ T)
    (hMesh : ∀ k : ℕ, k < N →
       X.drift * ((ts (k + 1) : ℝ) - (ts k : ℝ)) ≤ b) :
    ∀ᵐ ω ∂P, (T : ℝ≥0∞) < barrierRuinTime X 0 ω →
      X.drift * (ts 0 : ℝ) - X.X (ts 0) ω <
        X.drift * (ts N : ℝ) - X.X (ts N) ω →
      ∃ k : ℕ, k < N ∧
        0 < (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) -
          (X.drift * (ts k : ℝ) - X.X (ts k) ω) ∧
        (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) -
          (X.drift * (ts k : ℝ) - X.X (ts k) ω) ≤ b := by
  filter_upwards [bv_strict_zero_ruin_deficit_increment_band_ae X hBV] with ω hBand
  intro hSurv hPositive
  have hCell (k : ℕ) (hk : k < N) :
      0 ≤ (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) -
        (X.drift * (ts k : ℝ) - X.X (ts k) ω) ∧
      (X.drift * (ts (k + 1) : ℝ) - X.X (ts (k + 1)) ω) -
        (X.drift * (ts k : ℝ) - X.X (ts k) ω) ≤ b := by
    obtain ⟨hLower, hUpper⟩ :=
      hBand T hSurv (ts k) (ts (k + 1)) (hStep k hk) (hWithin k hk)
    exact ⟨hLower, hUpper.trans (hMesh k hk)⟩
  exact positive_grid_deficit_has_small_positive_increment
    (fun k => X.drift * (ts k : ℝ) - X.X (ts k) ω)
    N b hPositive hCell
