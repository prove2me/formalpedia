-- Prove2me | solution 1 for AvramDividend.Classical.bv_dyadic_active_count_refinement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:11:44.823921+00:00
-- url     : https://prove2.me/submissions/e00e5492-2801-430d-9759-f3dbb4e493ab

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset

/-- Refinement cannot decrease the number of intervals where the residual increases. -/
theorem solution (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range n,
      (ite (f (2 * i) < f (2 * i + 2)) (1 : ℕ) 0)) ≤
      ∑ i ∈ range (2 * n),
        (ite (f i < f (i + 1)) (1 : ℕ) 0) := by
  classical
  have hchild (x y z : ℝ) :
      (ite (x < z) (1 : ℕ) 0) ≤
        (ite (x < y) (1 : ℕ) 0) +
          (ite (y < z) (1 : ℕ) 0) := by
    by_cases hxz : x < z
    · by_cases hxy : x < y
      · simp [hxz, hxy]
      · have hyz : y < z := lt_of_le_of_lt (le_of_not_gt hxy) hxz
        simp [hxz, hxy, hyz]
    · simp [hxz]
  have hPair (g : ℕ → ℕ) (m : ℕ) :
      (∑ i ∈ range (2 * m), g i) =
        ∑ i ∈ range m, (g (2 * i) + g (2 * i + 1)) := by
    induction m with
    | zero => simp
    | succ m ih =>
      calc
        (∑ i ∈ range (2 * (m + 1)), g i) =
          ∑ i ∈ range (2 * m + 2), g i := by congr 1
        _ = (∑ i ∈ range (2 * m), g i) +
            g (2 * m) + g (2 * m + 1) := by
              rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega,
                sum_range_succ, sum_range_succ]
        _ = ∑ i ∈ range (m + 1), (g (2 * i) + g (2 * i + 1)) := by
              rw [sum_range_succ, ← ih]
              omega
  calc
    (∑ i ∈ range n,
      (ite (f (2 * i) < f (2 * i + 2)) (1 : ℕ) 0)) ≤
      ∑ i ∈ range n,
        ((ite (f (2 * i) < f (2 * i + 1)) (1 : ℕ) 0) +
          (ite (f (2 * i + 1) < f (2 * i + 2)) (1 : ℕ) 0)) := by
            apply sum_le_sum
            intro i _
            exact hchild (f (2 * i)) (f (2 * i + 1)) (f (2 * i + 2))
    _ = ∑ i ∈ range (2 * n),
        (ite (f i < f (i + 1)) (1 : ℕ) 0) := by
          rw [hPair]
