-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_positive_clock_refining_Y_grid_small
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T22:21:51.224933+00:00
-- url     : https://prove2.me/submissions/1e8497d5-b6d6-401a-891c-8b8cc735ba95

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_positive_compact_physical_Y_cell_modulus
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Time-mesh refinement forces genuine original Y increments to vanish away from zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      ∀ (a b : ℝ≥0) (ha : 0 < a)
        (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ),
        let Y : ℝ≥0 → ℝ := fun t =>
          X.X t ω + ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
        (∀ m i, i < n m →
          u m i ∈ Set.Icc a b ∧ u m (i + 1) ∈ Set.Icc a b) →
        (∀ δ : ℝ, 0 < δ →
          ∀ᶠ m in Filter.atTop,
            ∀ i, i < n m → dist (u m (i + 1)) (u m i) < δ) →
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ m in Filter.atTop,
            ∀ i, i < n m →
              |Y (u m (i + 1)) - Y (u m i)| < ε := by
  filter_upwards [avram_p3_f2_original_positive_compact_physical_Y_cell_modulus
    X hBV] with ω hModulus
  intro a b ha u n Y hInside hFine ε hε
  obtain ⟨δ, hδ, hCells⟩ := hModulus a b ha ε hε
  filter_upwards [hFine δ hδ] with m hm
  exact hCells (u m) (n m) (hInside m) hm
