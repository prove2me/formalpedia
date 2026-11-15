-- Prove2me | solution 1 for AvramDividend.Classical.avram_b236_discounted_original_continuous_stieltjes_finite_mesh_cash_terminal_value_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:05:40.039889+00:00
-- url     : https://prove2.me/submissions/f6aad060-1c83-4fa8-a7a6-7c687fb0f0d0

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology MeasureTheory
open scoped NNReal BigOperators
noncomputable section

theorem solution
    (q : ℝ) (hq : 0 ≤ q)
    (t : ℕ → ℝ≥0) (ht : Monotone t)
    (V cash : ℕ → ℝ) (n : ℕ)
    (hV : ∀ i ≤ n, 0 ≤ V i)
    (hCash : ∀ i < n, cash i ≤ V i - V (i + 1)) :
    (∑ i ∈ Finset.range n,
      Real.exp (-(q * (t i : ℝ))) * cash i) +
      Real.exp (-(q * (t n : ℝ))) * V n ≤
        Real.exp (-(q * (t 0 : ℝ))) * V 0 := by
  let d : ℕ → ℝ := fun i => Real.exp (-(q * (t i : ℝ)))
  have hd (i : ℕ) : 0 ≤ d i := (Real.exp_pos _).le
  have hdmono (i : ℕ) : d (i + 1) ≤ d i := by
    dsimp [d]
    apply Real.exp_le_exp.mpr
    have htime : (t i : ℝ) ≤ (t (i + 1) : ℝ) := by
      exact_mod_cast ht (Nat.le_succ i)
    nlinarith [mul_nonneg hq (sub_nonneg.mpr htime)]
  have hstep (i : ℕ) (hi : i < n) :
      d i * cash i + d (i + 1) * V (i + 1) ≤ d i * V i := by
    have hc := mul_le_mul_of_nonneg_left (hCash i hi) (hd i)
    have hv := mul_le_mul_of_nonneg_right (hdmono i)
      (hV (i + 1) (Nat.succ_le_of_lt hi))
    nlinarith
  have hclaim (k : ℕ) : k ≤ n →
      (∑ i ∈ Finset.range k, d i * cash i) + d k * V k ≤ d 0 * V 0 := by
    induction k with
    | zero =>
      intro _
      simp
    | succ k ih =>
      intro hk
      have hprev := ih (Nat.le_trans (Nat.le_succ k) hk)
      have hcurrent := hstep k (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)
      rw [Finset.sum_range_succ]
      linarith
  simpa only [d] using hclaim n le_rfl
