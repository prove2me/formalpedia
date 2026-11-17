-- Prove2me | solution 1 for BranchFull.small_ratio_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:18:12.63625+00:00
-- url     : https://prove2.me/submissions/04a75a49-dba4-4562-ae94-5ba8ac31a71f

import Mathlib
open MeasureTheory Set Filter Topology


theorem BranchFull.small_ratio_lt_half (t : ℝ) (ht : 0 < t) (hc : t ≤ 1/10000) :
    (fun (t : ℝ) => ((t⁻¹)^2+t⁻¹)*Real.exp (-t⁻¹+(10000+1/4)*t)) t < 1/2 := by
  simp only
  set s := t⁻¹ with hs
  have hs1 : 10000 ≤ s := by
    rw [hs, le_inv_comm₀ (by norm_num) ht]; linarith
  have hb : (10000+1/4)*t ≤ 2 := by nlinarith
  have he2 : Real.exp ((10000+1/4)*t) ≤ Real.exp 2 := Real.exp_le_exp.2 hb
  have hE2 : Real.exp 2 < 8 := by
    have := Real.exp_one_lt_d9
    rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith [Real.exp_pos 1]
  have h3 : s ^ 3 / (Nat.factorial 3) ≤ Real.exp s := Real.pow_div_factorial_le_exp (x := s) (by linarith) 3
  norm_num [Nat.factorial] at h3
  rw [Real.exp_add, Real.exp_neg]
  have hpos : 0 < Real.exp s := Real.exp_pos _
  have hpos2 : 0 < Real.exp ((10000+1/4)*t) := Real.exp_pos _
  rw [show (s ^ 2 + s) * ((Real.exp s)⁻¹ * Real.exp ((10000 + 1 / 4) * t)) =
      (s ^ 2 + s) * Real.exp ((10000 + 1 / 4) * t) / Real.exp s by field_simp]
  rw [div_lt_iff₀ hpos]
  have : (s ^ 2 + s) * Real.exp ((10000 + 1 / 4) * t) ≤ (s ^ 2 + s) * 8 := by
    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith

theorem solution (t : ℝ) (ht : 0 < t) (hc : t ≤ 1/10000) :
    (fun (t : ℝ) => ((t⁻¹)^2+t⁻¹)*Real.exp (-t⁻¹+(10000+1/4)*t)) t < 1/2 := by
  simp only
  set s := t⁻¹ with hs
  have hs1 : 10000 ≤ s := by
    rw [hs, le_inv_comm₀ (by norm_num) ht]; linarith
  have hb : (10000+1/4)*t ≤ 2 := by nlinarith
  have he2 : Real.exp ((10000+1/4)*t) ≤ Real.exp 2 := Real.exp_le_exp.2 hb
  have hE2 : Real.exp 2 < 8 := by
    have := Real.exp_one_lt_d9
    rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith [Real.exp_pos 1]
  have h3 : s ^ 3 / (Nat.factorial 3) ≤ Real.exp s := Real.pow_div_factorial_le_exp (x := s) (by linarith) 3
  norm_num [Nat.factorial] at h3
  rw [Real.exp_add, Real.exp_neg]
  have hpos : 0 < Real.exp s := Real.exp_pos _
  have hpos2 : 0 < Real.exp ((10000+1/4)*t) := Real.exp_pos _
  rw [show (s ^ 2 + s) * ((Real.exp s)⁻¹ * Real.exp ((10000 + 1 / 4) * t)) =
      (s ^ 2 + s) * Real.exp ((10000 + 1 / 4) * t) / Real.exp s by field_simp]
  rw [div_lt_iff₀ hpos]
  have : (s ^ 2 + s) * Real.exp ((10000 + 1 / 4) * t) ≤ (s ^ 2 + s) * 8 := by
    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith
