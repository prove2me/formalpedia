-- Prove2me | solution 1 for DerivativeChainPrivate.mixed_product_variation
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-18T01:58:01.895109+00:00
-- url     : https://prove2.me/submissions/4c7bce19-0167-467b-80bf-6f4af2cb6721

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators

theorem solution (G J : ℕ → ℝ) (hG : Monotone G) (hJ : Antitone J)
    (hG0 : ∀ k, 0 ≤ G k) (hJ0 : ∀ k, 0 ≤ J k) (n : ℕ) :
    (∑ k ∈ Finset.range n, |G (k + 1) * J (k + 1) - G k * J k|) ≤
      2 * G n * J 0 - G 0 * J 0 - G n * J n := by
  induction n with
  | zero => simp; ring_nf; exact le_rfl
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hstep : |G (n + 1) * J (n + 1) - G n * J n| ≤
        J n * (G (n + 1) - G n) + G (n + 1) * (J n - J (n + 1)) := by
      have hinc := mul_nonneg (hJ0 n) (sub_nonneg.mpr (hG (Nat.le_succ n)))
      have hdec := mul_nonneg (hG0 (n + 1)) (sub_nonneg.mpr (hJ (Nat.le_succ n)))
      apply abs_le.mpr
      constructor <;> nlinarith only [hinc, hdec]
    have hcross := mul_nonneg (sub_nonneg.mpr (hG (Nat.le_succ n)))
      (sub_nonneg.mpr (hJ (Nat.zero_le n)))
    nlinarith only [ih, hstep, hcross]
