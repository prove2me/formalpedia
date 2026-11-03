-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_stopped_finite_predictable_grid_X_L1_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:49:45.632274+00:00
-- url     : https://prove2.me/submissions/8efb1099-cbb2-4ca9-a4c6-9ba980ab49a6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_finite_predictable_grid_centered_X_L1_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Genuine stopped original predictable finite-grid scalar martingale
has zero total expectation, with explicit integrability assumptions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ)
    (grid : ℕ → ℝ≥0) (hGrid : Monotone grid)
    (H : ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (hWPast : ∀ i ∈ Finset.range n,
      Measurable[𝓕 (grid i)]
        (fun ω => if i < τ ω then H i ω else 0))
    (hWI : ∀ i ∈ Finset.range n,
      Integrable (fun ω => if i < τ ω then H i ω else 0) P)
    (hXI : ∀ i ∈ Finset.range n,
      Integrable (X.X (grid (i + 1) - grid i)) P)
    (hCellI : ∀ i ∈ Finset.range n, Integrable (fun ω =>
      (if i < τ ω then H i ω else 0) *
        (X.X (grid i + (grid (i + 1) - grid i)) ω -
          X.X (grid i) ω -
            (∫ η, X.X (grid (i + 1) - grid i) η ∂P))) P) :
    (∫ ω, ∑ i ∈ Finset.range n,
      (if i < τ ω then H i ω else 0) *
        (X.X (grid (i + 1)) ω - X.X (grid i) ω -
          (∫ η, X.X (grid (i + 1) - grid i) η ∂P)) ∂P) = 0 := by
  have hNext : ∀ i : ℕ,
      grid i + (grid (i + 1) - grid i) = grid (i + 1) := by
    intro i
    exact add_tsub_cancel_of_le (hGrid (Nat.le_succ i))
  have hz :=
    avram_wave7_06_original_finite_predictable_grid_centered_X_L1_zero
      X n grid (fun i => grid (i + 1) - grid i)
        (fun i ω => if i < τ ω then H i ω else 0)
          hWPast hWI hXI hCellI
  simpa only [hNext] using hz
