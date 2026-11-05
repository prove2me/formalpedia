-- Prove2me | solution 1 for AvramDividend.Classical.avram_leanlevy_bridge_original_equal_mesh_triangular_rate_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:46:44.087269+00:00
-- url     : https://prove2.me/submissions/0ea66d81-b59e-4324-97b8-568e4402db96

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    (T a : ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range m,
      (((i : ℝ) * T) / (m : ℝ) * a) *
        (((((i : ℝ) + 1) * T) / (m : ℝ) -
          ((i : ℝ) * T) / (m : ℝ)) * a)) =
      ((m : ℝ) * ((m : ℝ) - 1) / 2) *
        ((T * a) ^ 2 / (m : ℝ) ^ 2) := by
  have hsum (k : ℕ) :
      (∑ i ∈ Finset.range k, (i : ℝ)) =
        (k : ℝ) * ((k : ℝ) - 1) / 2 := by
    induction k with
    | zero => simp
    | succ k hk =>
        rw [Finset.sum_range_succ, hk]
        push_cast
        ring
  calc
    (∑ i ∈ Finset.range m,
      (((i : ℝ) * T) / (m : ℝ) * a) *
        (((((i : ℝ) + 1) * T) / (m : ℝ) -
          ((i : ℝ) * T) / (m : ℝ)) * a)) =
      ∑ i ∈ Finset.range m,
        (i : ℝ) * ((T * a) ^ 2 / (m : ℝ) ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = ((m : ℝ) * ((m : ℝ) - 1) / 2) *
          ((T * a) ^ 2 / (m : ℝ) ^ 2) := by
          rw [← Finset.sum_mul, hsum m]
