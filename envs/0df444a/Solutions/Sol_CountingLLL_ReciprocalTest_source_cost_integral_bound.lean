-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.source_cost_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:46:04.161955+00:00
-- url     : https://prove2.me/submissions/1e55fa83-4307-474a-b465-a8f78d8125c9

import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Interval

private noncomputable def q (t : ℝ) : ℝ :=
  (∑ k ∈ Finset.range 10, 3*(27/40:ℝ)^k*t^(k+1)) +
    (3*(27/40:ℝ)^10/(1-27/40))*t^11

private theorem q_int : (∫ t in (0:ℝ)..1, q t) < (74/25:ℝ) := by
  unfold q
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_finset_sum]
    · simp only [intervalIntegral.integral_const_mul, integral_pow]
      norm_num [Finset.sum_range_succ]
    · intro i hi
      exact ((continuous_const.mul (continuous_id.pow _)).intervalIntegrable _ _)
  · exact (continuous_finset_sum _ fun k hk => continuous_const.mul (continuous_id.pow _)).intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_id.pow _)).intervalIntegrable _ _

private theorem q_bound (θ t : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 9/40)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 3*t/(1-3*θ*t) ≤ q t := by
  let c : ℝ := 27/40
  let x : ℝ := c*t
  have hc0 : 0 ≤ c := by norm_num [c]
  have hc1 : c < 1 := by norm_num [c]
  have hx0 : 0 ≤ x := mul_nonneg hc0 ht0
  have hxc : x ≤ c := by dsimp [x]; nlinarith
  have hx1 : x < 1 := lt_of_le_of_lt hxc hc1
  have hden : 0 < 1-x := by linarith
  have hden' : 0 < 1-3*θ*t := by dsimp [x,c] at *; nlinarith
  have hθx : 3*θ*t ≤ x := by dsimp [x,c]; nlinarith
  have hfirst : 3*t/(1-3*θ*t) ≤ 3*t/(1-x) := by
    apply div_le_div_of_nonneg_left (by positivity) hden
    linarith
  have hgeom : (∑ k ∈ Finset.range 10, x^k) + x^10/(1-x) = 1/(1-x) := by
    have h := geom_sum_mul_neg x 10
    field_simp
    linarith
  have htail : x^10/(1-x) ≤ x^10/(1-c) := by
    apply div_le_div_of_nonneg_left (pow_nonneg hx0 _) (by linarith : 0 < 1-c)
    linarith
  have hsum : q t = 3*t*((∑ k ∈ Finset.range 10, x^k) + x^10/(1-c)) := by
    unfold q
    dsimp [x, c]
    rw [mul_add, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      rw [mul_pow, pow_succ]
      ring
    · ring
  rw [hsum]
  calc
    _ ≤ 3*t/(1-x) := hfirst
    _ = 3*t*((∑ k ∈ Finset.range 10, x^k) + x^10/(1-x)) := by rw [hgeom]; ring
    _ ≤ 3*t*((∑ k ∈ Finset.range 10, x^k) + x^10/(1-c)) := by gcongr

/-- The paper's uniform upper bound for the source cost integral. -/
theorem solution (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 9/40) :
    (∫ t in (0:ℝ)..1, 3*t/(1-3*θ*t)) < (74/25:ℝ) := by
  have hden (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : 1-3*θ*t ≠ 0 := by
    have hh : 0 ≤ ((9/40:ℝ)-θ)*t := mul_nonneg (sub_nonneg.mpr hθ1) ht.1
    have ht1 : t ≤ 1 := ht.2
    have hp : 0 < 1-3*θ*t := by nlinarith
    linarith
  have hcont : ContinuousOn (fun t : ℝ => 3*t/(1-3*θ*t)) (Set.Icc 0 1) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · exact hden
  have hi : IntervalIntegrable (fun t : ℝ => 3*t/(1-3*θ*t)) volume 0 1 := hcont.intervalIntegrable_of_Icc (by norm_num : (0:ℝ) ≤ 1)
  have hq : IntervalIntegrable q volume 0 1 := by
    unfold q
    exact ((continuous_finset_sum _ fun k hk => continuous_const.mul (continuous_id.pow _)).add
      (continuous_const.mul (continuous_id.pow _))).intervalIntegrable _ _
  have hle : (∫ t in (0:ℝ)..1, 3*t/(1-3*θ*t)) ≤ ∫ t in (0:ℝ)..1, q t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hi hq
    intro t ht
    exact q_bound θ t hθ0 hθ1 ht.1 ht.2
  exact lt_of_le_of_lt hle q_int
