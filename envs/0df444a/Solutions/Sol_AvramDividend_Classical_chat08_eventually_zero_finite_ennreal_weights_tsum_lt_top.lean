-- Prove2me | solution 1 for AvramDividend.Classical.chat08_eventually_zero_finite_ennreal_weights_tsum_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:24:16.148248+00:00
-- url     : https://prove2.me/submissions/8ac34277-cba0-416a-ba7c-abd424c6ff72

import Mathlib

open scoped NNReal ENNReal
theorem solution
    (w : ℕ → ℝ≥0∞)
    (hfinite : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → w n = 0)
    (hterms : ∀ n, w n < ⊤) :
    (∑' n : ℕ, w n) < ⊤ := by
  obtain ⟨N, hN⟩ := hfinite
  rw [tsum_eq_sum (s := Finset.range N) (fun n hn => hN n (by simpa using hn))]
  exact ENNReal.sum_lt_top.2 fun n _ => hterms n
