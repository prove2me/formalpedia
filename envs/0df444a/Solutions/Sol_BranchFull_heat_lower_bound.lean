-- Prove2me | solution 1 for BranchFull.heat_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:18:13.614147+00:00
-- url     : https://prove2.me/submissions/e5013010-f489-4a33-8544-2c0495315fb4

import Mathlib
open MeasureTheory Set Filter Topology


theorem BranchFull.small_ratio_lt_half_aux (t : ℝ) (ht : 0 < t) (hc : t ≤ 1/10000) :
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

theorem BranchFull.large_ratio_lt_half_aux (t : ℝ) (ht : 1/10000 ≤ t) :
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

theorem BranchFull.heat_lower_bound (K : ℝ → ℝ)
    (hs : ∀ t > 0, t ≤ 1/10000 →
      Real.exp (-10000*t)*(1-(fun (t : ℝ) => ((t⁻¹)^2+t⁻¹)*Real.exp (-t⁻¹+(10000+1/4)*t)) t) ≤ K t)
    (hl : ∀ t > 0, 1/10000 ≤ t →
      Real.exp (-10000*t)*(1-(fun (t : ℝ) => (1000000+t⁻¹)*Real.exp (-(1000000-10000-1/4)*t)) t) ≤ K t) :
    ∀ t > 0, (1/2)*Real.exp (-10000*t) < K t := by
  intro t ht
  have hE := Real.exp_pos (-10000*t)
  rcases le_total t (1/10000) with h | h
  · have := hs t ht h
    have hr := BranchFull.small_ratio_lt_half_aux t ht h
    simp only at this hr
    nlinarith
  · have := hl t ht h
    have hr := BranchFull.large_ratio_lt_half_aux t h
    simp only at this hr
    nlinarith

theorem solution (K : ℝ → ℝ)
    (hs : ∀ t > 0, t ≤ 1/10000 →
      Real.exp (-10000*t)*(1-(fun (t : ℝ) => ((t⁻¹)^2+t⁻¹)*Real.exp (-t⁻¹+(10000+1/4)*t)) t) ≤ K t)
    (hl : ∀ t > 0, 1/10000 ≤ t →
      Real.exp (-10000*t)*(1-(fun (t : ℝ) => (1000000+t⁻¹)*Real.exp (-(1000000-10000-1/4)*t)) t) ≤ K t) :
    ∀ t > 0, (1/2)*Real.exp (-10000*t) < K t := by
  intro t ht
  have hE := Real.exp_pos (-10000*t)
  rcases le_total t (1/10000) with h | h
  · have := hs t ht h
    have hr := BranchFull.small_ratio_lt_half_aux t ht h
    simp only at this hr
    nlinarith
  · have := hl t ht h
    have hr := BranchFull.large_ratio_lt_half_aux t h
    simp only at this hr
    nlinarith
