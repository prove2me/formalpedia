-- Prove2me | solution 1 for AzumaWeightedSums.Multiplicative.convexity_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T09:55:55.652293+00:00
-- url     : https://prove2.me/submissions/448abaa0-9520-4f7d-8328-ad498e0159e4

import Mathlib

set_option autoImplicit false

theorem solution (t b x : ℝ) (hb : b ≠ 0) (hx : |x| ≤ 1) :
    Real.exp (t * b * x) ≤
      Real.cosh (t * |b|) + (b * x / |b|) * Real.sinh (t * |b|) := by
  have hab : 0 < |b| := abs_pos.mpr hb
  set y := b * x / |b| with hy
  have hy1 : |y| ≤ 1 := by
    rw [hy, abs_div, abs_mul, abs_abs, mul_div_assoc, mul_comm, div_mul_cancel₀ _ hab.ne']
    exact hx
  have hyl : -1 ≤ y := (abs_le.mp hy1).1
  have hyu : y ≤ 1 := (abs_le.mp hy1).2
  have key : t * b * x = ((1 + y) / 2) * (t * |b|) + ((1 - y) / 2) * (-(t * |b|)) := by
    rw [hy]; field_simp; ring
  have hc := convexOn_exp.2 (Set.mem_univ (t * |b|)) (Set.mem_univ (-(t * |b|)))
    (show (0:ℝ) ≤ (1 + y) / 2 by linarith) (show (0:ℝ) ≤ (1 - y) / 2 by linarith)
    (by ring)
  simp only [smul_eq_mul] at hc
  rw [key]
  refine hc.trans (le_of_eq ?_)
  rw [Real.cosh_eq, Real.sinh_eq]
  ring
