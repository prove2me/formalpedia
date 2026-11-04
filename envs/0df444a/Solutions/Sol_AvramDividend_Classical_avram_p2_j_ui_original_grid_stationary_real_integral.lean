-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_original_grid_stationary_real_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:47:57.027193+00:00
-- url     : https://prove2.me/submissions/7f72447e-de06-4ac3-b76d-0bae67078925

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal BigOperators

/-- Original finite grids have exact real-test means from stationary cell laws. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (n : ℕ) (grid : ℕ → ℝ≥0)
    (hGrid : ∀ i : ℕ, i < n → grid i ≤ grid (i + 1))
    (g : ℝ → ℝ) (hg : Measurable g)
    (hInt : ∀ i < n, Integrable
      (fun ω => g (X.X ((s + grid (i + 1)) - (s + grid i)) ω)) P) :
    (∫ ω, ∑ i ∈ Finset.range n,
      g (X.X (s + grid (i + 1)) ω - X.X (s + grid i) ω) ∂P) =
    ∑ i ∈ Finset.range n,
      ∫ ω, g (X.X ((s + grid (i + 1)) - (s + grid i)) ω) ∂P := by
  have hLaw (i : ℕ) (hi : i ∈ Finset.range n) :
      IdentDistrib
        (fun ω => g (X.X (s + grid (i + 1)) ω - X.X (s + grid i) ω))
        (fun ω => g (X.X ((s + grid (i + 1)) - (s + grid i)) ω)) P P := by
    have hTime : s + grid i ≤ s + grid (i + 1) := by
      have h := add_le_add_left (hGrid i (Finset.mem_range.mp hi)) s
      simpa only [add_comm s] using h
    simpa only [Function.comp_def] using
      (X.stationaryIncrements (s + grid i) (s + grid (i + 1)) hTime).comp hg
  calc
    (∫ ω, ∑ i ∈ Finset.range n,
      g (X.X (s + grid (i + 1)) ω - X.X (s + grid i) ω) ∂P) =
      ∑ i ∈ Finset.range n,
        ∫ ω, g (X.X (s + grid (i + 1)) ω - X.X (s + grid i) ω) ∂P := by
          apply integral_finset_sum
          intro i hi
          exact (hLaw i hi).integrable_iff.mpr (hInt i (Finset.mem_range.mp hi))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hLaw i hi).integral_eq
