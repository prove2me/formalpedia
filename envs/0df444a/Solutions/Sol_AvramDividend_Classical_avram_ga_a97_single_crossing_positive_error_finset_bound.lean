-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a97_single_crossing_positive_error_finset_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:38:18.502659+00:00
-- url     : https://prove2.me/submissions/c21e9f50-0790-4006-a8be-e0539f797cbb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- A stopped physical Gaussian mesh with at most one crossing cell pays at most one positive terminal error budget. -/
theorem solution (S : Finset ℕ) (f : ℕ → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hCard : S.card ≤ 1)
    (hBound : ∀ i ∈ S, max (f i) 0 ≤ B) :
    (∑ i ∈ S, max (f i) 0) ≤ B := by
  have hBoundSum :
      (∑ i ∈ S, max (f i) 0) ≤ ∑ i ∈ S, B :=
    Finset.sum_le_sum hBound
  have hNum : (S.card : ℝ) ≤ 1 := by exact_mod_cast hCard
  have hMul : (S.card : ℝ) * B ≤ 1 * B :=
    mul_le_mul_of_nonneg_right hNum hB
  calc
    (∑ i ∈ S, max (f i) 0) ≤ ∑ i ∈ S, B := hBoundSum
    _ = (S.card : ℝ) * B := by simp
    _ ≤ 1 * B := hMul
    _ = B := one_mul _
