-- Prove2me | solution 1 for CountingLLL.ContractedWalk.cubic_fixed_point_unique
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:11:59.618297+00:00
-- url     : https://prove2.me/submissions/fb8b7e6a-a5fa-493d-b7a3-eb972a8eeecc

import Mathlib
set_option autoImplicit false

theorem solution (θ z g h : ℝ) (ht0 : 0 ≤ θ) (ht : θ < 1/3)
    (hz0 : 0 ≤ z) (hz : z ≤ 1) (hg0 : 0 ≤ g) (hg : g ≤ 1) (hh0 : 0 ≤ h) (hh : h ≤ 1)
    (hgEq : g = 1-θ+θ*z*g^3) (hhEq : h = 1-θ+θ*z*h^3) : g = h := by
  have hg2 : g^2 ≤ 1 := by nlinarith [mul_nonneg hg0 (sub_nonneg.mpr hg)]
  have hh2 : h^2 ≤ 1 := by nlinarith [mul_nonneg hh0 (sub_nonneg.mpr hh)]
  have hgh : g*h ≤ 1 := by nlinarith [mul_nonneg hg0 (sub_nonneg.mpr hh)]
  have hs0 : 0 ≤ g^2+g*h+h^2 := by positivity
  have hs : g^2+g*h+h^2 ≤ 3 := by nlinarith
  have htz0 : 0 ≤ θ*z := mul_nonneg ht0 hz0
  have htz : θ*z ≤ θ := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hz)]
  have hterm : θ*z*(g^2+g*h+h^2) ≤ 3*θ := by
    nlinarith [mul_nonneg htz0 (sub_nonneg.mpr hs), mul_nonneg (sub_nonneg.mpr htz) (by norm_num : (0:ℝ) ≤ 3)]
  have hpos : 0 < 1-θ*z*(g^2+g*h+h^2) := by nlinarith
  have hd : (g-h)*(1-θ*z*(g^2+g*h+h^2)) = 0 := by nlinarith [hgEq,hhEq]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_right (ne_of_gt hpos))
