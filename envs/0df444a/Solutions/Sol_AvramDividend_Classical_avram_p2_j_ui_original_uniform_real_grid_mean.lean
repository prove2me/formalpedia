-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_original_uniform_real_grid_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:56:44.39417+00:00
-- url     : https://prove2.me/submissions/fcf85b2c-8755-48ac-864c-18704d16380d

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_cell_width
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_grid_stationary_real_integral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal BigOperators

/-- Every original uniform-grid real-test mean is the true source one-cell mean times the cell count. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) (g : ℝ → ℝ) (hg : Measurable g)
    (hInt : Integrable
      (fun ω => g (X.X (T / ((n : ℝ≥0) + 1)) ω)) P) :
    (∫ ω, ∑ i ∈ Finset.range (n + 1),
      g (X.X ((↑(i + 1) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
         X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) ∂P) =
    ((n : ℝ) + 1) *
      (∫ ω, g (X.X (T / ((n : ℝ≥0) + 1)) ω) ∂P) := by
  let δ : ℝ≥0 := T / ((n : ℝ≥0) + 1)
  have hGrid : ∀ i : ℕ, i < n + 1 →
      (i : ℝ≥0) * δ ≤ ((i + 1 : ℕ) : ℝ≥0) * δ := by
    intro i hi
    gcongr
    exact Nat.le_succ i
  have hIntCells : ∀ i < n + 1, Integrable
      (fun ω => g (X.X (((i + 1 : ℕ) : ℝ≥0) * δ -
        (i : ℝ≥0) * δ) ω)) P := by
    intro i hi
    simpa only [δ, avram_p2_a_zero_rate_uniform_cell_width] using hInt
  have hMean := avram_p2_j_ui_original_grid_stationary_real_integral
    X 0 (n + 1) (fun i => (i : ℝ≥0) * δ) hGrid g hg
    (by intro i hi
        simpa only [zero_add] using hIntCells i hi)
  calc
    (∫ ω, ∑ i ∈ Finset.range (n + 1),
      g (X.X ((↑(i + 1) : ℝ≥0) * δ) ω -
         X.X ((i : ℝ≥0) * δ) ω) ∂P) =
      ∑ i ∈ Finset.range (n + 1),
        ∫ ω, g (X.X δ ω) ∂P := by
          simpa only [zero_add, avram_p2_a_zero_rate_uniform_cell_width] using hMean
    _ = ((n : ℝ) + 1) * (∫ ω, g (X.X δ ω) ∂P) := by
      simp [Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul, Nat.cast_add]
