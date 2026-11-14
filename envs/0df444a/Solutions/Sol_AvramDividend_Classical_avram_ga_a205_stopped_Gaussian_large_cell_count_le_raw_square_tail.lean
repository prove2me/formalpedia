-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a205_stopped_Gaussian_large_cell_count_le_raw_square_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:03:29.385292+00:00
-- url     : https://prove2.me/submissions/0c32725f-5b00-472e-b5ed-1ab0cd8004ef

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
noncomputable section

/-- Actual stopped physical Gaussian cells with a large raw increment are
counted by the square-tail energy with the inverse threshold-square weight. -/
theorem solution
    (S : Finset ℕ) (A : ℕ → Prop) [DecidablePred A]
    (R : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    (∑ i ∈ S, if A i then
      (if δ ≤ |R i| then (1 : ℝ) else 0) else 0) ≤
    (∑ i ∈ S, if A i then
      (if δ ≤ |R i| then (R i)^2 / δ^2 else 0) else 0) := by
  classical
  apply Finset.sum_le_sum
  intro i hi
  by_cases ha : A i
  · by_cases ht : δ ≤ |R i|
    · have hsq : δ^2 ≤ (R i)^2 := by
        have h0 : 0 ≤ |R i| := abs_nonneg _
        have hprod : 0 ≤ (|R i| - δ) * (|R i| + δ) :=
          mul_nonneg (sub_nonneg.mpr ht)
            (add_nonneg h0 (le_of_lt hδ))
        nlinarith [sq_abs (R i)]
      have hd : 1 ≤ (R i)^2 / δ^2 :=
        (le_div_iff₀ (sq_pos_of_pos hδ)).2 (by nlinarith)
      simpa only [if_pos ha,if_pos ht] using hd
    · simp only [if_pos ha,if_neg ht]
      exact le_refl (0 : ℝ)
  · simp only [if_neg ha]
    exact le_refl (0 : ℝ)
