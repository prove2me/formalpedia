-- Prove2me | solution 1 for BranchFull.large_ratio_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:18:11.784116+00:00
-- url     : https://prove2.me/submissions/04aed900-8ec6-43a2-8b1c-4a401a659743

import Mathlib
open MeasureTheory Set Filter Topology


theorem BranchFull.large_ratio_lt_half (t : ℝ) (ht : 1/10000 ≤ t) :
    (fun (t : ℝ) => (1000000+t⁻¹)*Real.exp (-(1000000-10000-1/4)*t)) t < 1/2 := by
  simp only
  have ht0 : 0 < t := by linarith
  have hinv : t⁻¹ ≤ 10000 := by
    rw [inv_le_comm₀ ht0 (by norm_num)]; linarith
  have hx : (98:ℝ) ≤ (1000000-10000-1/4)*t := by nlinarith
  have hexp : Real.exp 98 ≤ Real.exp ((1000000-10000-1/4)*t) := Real.exp_le_exp.2 hx
  have h4 : (98:ℝ) ^ 4 / (Nat.factorial 4) ≤ Real.exp 98 := Real.pow_div_factorial_le_exp (x := 98) (by norm_num) 4
  norm_num [Nat.factorial] at h4
  rw [show -(1000000-10000-1/4)*t = -((1000000-10000-1/4)*t) by ring, Real.exp_neg]
  have hpos : 0 < Real.exp ((1000000-10000-1/4)*t) := Real.exp_pos _
  rw [← div_eq_mul_inv, div_lt_iff₀ hpos]
  nlinarith

theorem solution (t : ℝ) (ht : 1/10000 ≤ t) :
    (fun (t : ℝ) => (1000000+t⁻¹)*Real.exp (-(1000000-10000-1/4)*t)) t < 1/2 := by
  simp only
  have ht0 : 0 < t := by linarith
  have hinv : t⁻¹ ≤ 10000 := by
    rw [inv_le_comm₀ ht0 (by norm_num)]; linarith
  have hx : (98:ℝ) ≤ (1000000-10000-1/4)*t := by nlinarith
  have hexp : Real.exp 98 ≤ Real.exp ((1000000-10000-1/4)*t) := Real.exp_le_exp.2 hx
  have h4 : (98:ℝ) ^ 4 / (Nat.factorial 4) ≤ Real.exp 98 := Real.pow_div_factorial_le_exp (x := 98) (by norm_num) 4
  norm_num [Nat.factorial] at h4
  rw [show -(1000000-10000-1/4)*t = -((1000000-10000-1/4)*t) by ring, Real.exp_neg]
  have hpos : 0 < Real.exp ((1000000-10000-1/4)*t) := Real.exp_pos _
  rw [← div_eq_mul_inv, div_lt_iff₀ hpos]
  nlinarith
