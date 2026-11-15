-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_physical_chronological_finite_grid_total_duration_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:46:19.969316+00:00
-- url     : https://prove2.me/submissions/027507a8-9876-4c5e-aca1-372016af2049

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    (t : ℕ → ℝ≥0) (n : ℕ) (T : ℝ≥0)
    (hn : t n ≤ T) :
    (∑ i ∈ Finset.range n,
      ((t (i + 1) : ℝ) - (t i : ℝ))) =
      (t n : ℝ) - (t 0 : ℝ) ∧
    (∑ i ∈ Finset.range n,
      ((t (i + 1) : ℝ) - (t i : ℝ))) ≤ (T : ℝ) := by
  have hTel (k : ℕ) :
      (∑ i ∈ Finset.range k,
        ((t (i + 1) : ℝ) - (t i : ℝ))) =
          (t k : ℝ) - (t 0 : ℝ) := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  refine ⟨hTel n, ?_⟩
  rw [hTel n]
  have htn : (t n : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast hn
  have ht0 : (0 : ℝ) ≤ (t 0 : ℝ) := NNReal.coe_nonneg _
  linarith
