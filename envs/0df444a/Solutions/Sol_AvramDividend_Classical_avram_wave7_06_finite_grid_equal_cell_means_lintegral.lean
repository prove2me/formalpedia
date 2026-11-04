-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_finite_grid_equal_cell_means_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:04:57.09719+00:00
-- url     : https://prove2.me/submissions/46516ef3-c877-4a39-9a8d-9cb3151e16b3

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators

/-- Equal finite-cell means sum to the expected source grid occupation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (m : ℕ)
    (F : ℕ → Ω → ENNReal) (q : ENNReal)
    (hMeas : ∀ i ∈ Finset.range m, Measurable (F i))
    (hEach : ∀ i ∈ Finset.range m, (∫⁻ ω, F i ω ∂P) = q) :
    (∫⁻ ω, ∑ i ∈ Finset.range m, F i ω ∂P) =
      (m : ENNReal) * q := by
  rw [lintegral_finset_sum (Finset.range m) hMeas]
  calc
    (∑ i ∈ Finset.range m, ∫⁻ ω, F i ω ∂P) =
        ∑ i ∈ Finset.range m, q := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hEach i hi
    _ = (m : ENNReal) * q := by
      simp [nsmul_eq_mul]
