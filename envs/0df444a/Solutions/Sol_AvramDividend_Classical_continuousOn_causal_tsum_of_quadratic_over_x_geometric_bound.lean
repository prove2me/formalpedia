-- Prove2me | solution 1 for AvramDividend.Classical.continuousOn_causal_tsum_of_quadratic_over_x_geometric_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:30:16.389242+00:00
-- url     : https://prove2.me/submissions/423f1b30-8e73-433a-aca1-25e73518b9a7

import Mathlib

open MeasureTheory Set Filter Topology
theorem solution
    (f : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hf : ∀ n : ℕ, ContinuousOn (f n) (Ioi (0 : ℝ)))
    (hbound : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      ‖f n x‖ ≤ ((n : ℝ) ^ 2 * ρ ^ n) / x) :
    ContinuousOn (fun x : ℝ => ∑' n : ℕ, f n x) (Ioi (0 : ℝ)) := by
  intro x hx
  have hx0 : (0:ℝ) < x := hx
  have hsum : Summable fun n : ℕ => ((n : ℝ) ^ 2 * ρ ^ n) / (x / 2) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one 2 (show ‖ρ‖ < 1 by
      rw [Real.norm_eq_abs, abs_of_pos hρ0]; exact hρ1)
    exact h.div_const _
  have hc : ContinuousOn (fun y : ℝ => ∑' n : ℕ, f n y) (Ioi (x / 2)) := by
    refine continuousOn_tsum (fun n => (hf n).mono ?_) hsum fun n y hy => ?_
    · intro y hy; exact lt_trans (by linarith) (show x / 2 < y from hy)
    · have hy0 : 0 < y := lt_trans (by linarith) (show x / 2 < y from hy)
      refine (hbound n y hy0).trans ?_
      exact div_le_div_of_nonneg_left (by positivity) (by linarith) (le_of_lt hy)
  exact (hc.continuousAt (Ioi_mem_nhds (by linarith))).continuousWithinAt
