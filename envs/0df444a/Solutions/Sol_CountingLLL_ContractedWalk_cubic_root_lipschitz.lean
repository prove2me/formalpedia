-- Prove2me | solution 1 for CountingLLL.ContractedWalk.cubic_root_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:13:48.22421+00:00
-- url     : https://prove2.me/submissions/bc47cd33-04c2-4acf-8919-d0b5964efea6

import Mathlib
set_option autoImplicit false

theorem solution (θ x y g h : ℝ) (ht0 : 0 ≤ θ) (ht : θ < 1/3)
    (hx0 : 0 ≤ x) (hx : x ≤ 1) (hy0 : 0 ≤ y) (hy : y ≤ 1)
    (hg0 : 0 ≤ g) (hg : g ≤ 1) (hh0 : 0 ≤ h) (hh : h ≤ 1)
    (hgEq : g = 1-θ+θ*x*g^3) (hhEq : h = 1-θ+θ*y*h^3) :
    |g-h| ≤ θ/(1-3*θ)*|x-y| := by
  have hg2 : g^2 ≤ 1 := by nlinarith [mul_nonneg hg0 (sub_nonneg.mpr hg)]
  have hh2 : h^2 ≤ 1 := by nlinarith [mul_nonneg hh0 (sub_nonneg.mpr hh)]
  have hgh : g*h ≤ 1 := by nlinarith [mul_nonneg hg0 (sub_nonneg.mpr hh)]
  have hs0 : 0 ≤ g^2+g*h+h^2 := by positivity
  have hs : g^2+g*h+h^2 ≤ 3 := by nlinarith
  have hp : |g^3-h^3| ≤ 3*|g-h| := by
    rw [show g^3-h^3 = (g-h)*(g^2+g*h+h^2) by ring, abs_mul, abs_of_nonneg hs0]
    nlinarith [mul_nonneg (abs_nonneg (g-h)) (sub_nonneg.mpr hs)]
  have hg3 : 0 ≤ g^3 := pow_nonneg hg0 _
  have hg3le : g^3 ≤ 1 := pow_le_one₀ hg0 hg
  have hpiece : |x*g^3-y*h^3| ≤ |x-y| + 3*|g-h| := by
    have heq : x*g^3-y*h^3 = (x-y)*g^3+y*(g^3-h^3) := by ring
    rw [heq]
    calc
      _ ≤ |(x-y)*g^3|+|y*(g^3-h^3)| := abs_add_le _ _
      _ = |x-y| * g^3 + y * |g^3-h^3| := by rw [abs_mul, abs_mul, abs_of_nonneg hg3, abs_of_nonneg hy0]
      _ ≤ |x-y|+3*|g-h| := by
        nlinarith [mul_nonneg (abs_nonneg (x-y)) (sub_nonneg.mpr hg3le),
          mul_nonneg (sub_nonneg.mpr hy) (abs_nonneg (g^3-h^3)), mul_nonneg hy0 (sub_nonneg.mpr hp)]
  have hdiff : g-h = θ*(x*g^3-y*h^3) := by nlinarith [hgEq,hhEq]
  have hdabs : |g-h| = θ*|x*g^3-y*h^3| := by rw [hdiff, abs_mul, abs_of_nonneg ht0]
  have hineq : |g-h| ≤ θ*(|x-y| + 3*|g-h|) := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hpiece)]
  have hden : 0 < 1-3*θ := by linarith
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).2
  nlinarith
