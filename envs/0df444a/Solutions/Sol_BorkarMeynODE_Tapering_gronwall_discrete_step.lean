-- Prove2me | solution 1 for BorkarMeynODE.Tapering.gronwall_discrete_step
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:50:23.924904+00:00
-- url     : https://prove2.me/submissions/d22f6196-cb60-4f97-ab2a-38391ad121b9

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option autoImplicit false

theorem solution (A α γ : ℕ → ℝ)
    (hA : ∀ n, 0 ≤ A n) (hα : ∀ n, 0 ≤ α n) (hγ : ∀ n, 0 ≤ γ n)
    (hrec : ∀ n : ℕ, A (n + 1) ≤ (1 + α n) * A n + γ n) :
    ∀ n : ℕ, 1 ≤ n →
      A (n + 1) ≤ Real.exp (∑ k ∈ Finset.Icc 1 n, α k) *
        ((1 + α 0) * A 0 + ∑ k ∈ Finset.range (n + 1), γ k) := by
  have hall : ∀ n : ℕ,
      A (n + 1) ≤ Real.exp (∑ k ∈ Finset.Icc 1 n, α k) *
        ((1 + α 0) * A 0 + ∑ k ∈ Finset.range (n + 1), γ k) := by
    intro n
    induction n with
    | zero => simpa using hrec 0
    | succ n ih =>
      have hfactor : 0 ≤ 1 + α (n + 1) := by linarith [hα (n + 1)]
      have hbase : 0 ≤ (1 + α 0) * A 0 + ∑ k ∈ Finset.range (n + 1), γ k := by
        exact add_nonneg (mul_nonneg (by linarith [hα 0]) (hA 0))
          (Finset.sum_nonneg (fun k _ => hγ k))
      have hexp : 1 ≤ Real.exp (∑ k ∈ Finset.Icc 1 (n + 1), α k) := by
        apply Real.one_le_exp_iff.mpr
        exact Finset.sum_nonneg (fun k _ => hα k)
      have hmul := mul_le_mul_of_nonneg_left ih hfactor
      have he : 1 + α (n + 1) ≤ Real.exp (α (n + 1)) := by
        simpa [add_comm] using Real.add_one_le_exp (α (n + 1))
      have hb := mul_le_mul_of_nonneg_right he
        (mul_nonneg (Real.exp_pos (∑ k ∈ Finset.Icc 1 n, α k)).le hbase)
      have hg := mul_le_mul_of_nonneg_right hexp (hγ (n + 1))
      rw [Finset.sum_range_succ]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), Real.exp_add] at hexp hg ⊢
      nlinarith [hrec (n + 1)]
  exact fun n _ => hall n
