-- Prove2me | solution 1 for BorkarMeynODE.Tapering.gronwall_discrete_sum
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:50:24.718834+00:00
-- url     : https://prove2.me/submissions/a040d06c-003c-4613-996d-cc73dda66dfa

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option autoImplicit false

theorem solution (A α : ℕ → ℝ) (β : ℝ)
    (hA : ∀ n, 0 ≤ A n) (hα : ∀ n, 0 ≤ α n) (hβ : 0 < β)
    (hrec : ∀ n : ℕ, A (n + 1) ≤ β + ∑ k ∈ Finset.range (n + 1), α k * A k) :
    ∀ n : ℕ, 1 ≤ n →
      A (n + 1) ≤ Real.exp (∑ k ∈ Finset.Icc 1 n, α k) * (α 0 * A 0 + β) := by
  have hbase : 0 ≤ α 0 * A 0 + β := add_nonneg (mul_nonneg (hα 0) (hA 0)) hβ.le
  have hb : ∀ n : ℕ, β + ∑ k ∈ Finset.range (n + 1), α k * A k ≤
      Real.exp (∑ k ∈ Finset.Icc 1 n, α k) * (α 0 * A 0 + β) := by
    intro n
    induction n with
    | zero => simp [add_comm]
    | succ n ih =>
      have ha := hα (n + 1)
      have hstep := mul_le_mul_of_nonneg_left (hrec n) ha
      have hfactor : 0 ≤ 1 + α (n + 1) := by linarith
      have hbound := mul_le_mul_of_nonneg_left ih hfactor
      have he : 1 + α (n + 1) ≤ Real.exp (α (n + 1)) := by
        simpa [add_comm] using Real.add_one_le_exp (α (n + 1))
      have hfinal := mul_le_mul_of_nonneg_right he
        (mul_nonneg (Real.exp_pos (∑ k ∈ Finset.Icc 1 n, α k)).le hbase)
      rw [Finset.sum_range_succ]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), Real.exp_add]
      nlinarith
  exact fun n _ => (hrec n).trans (hb n)
