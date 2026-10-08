-- Prove2me | solution 1 for AvramDividend.Classical.exp_negative_secant_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T20:21:16.0207+00:00
-- url     : https://prove2.me/submissions/77731b5c-26e4-41c5-bc2e-519fbb7ed218

import Mathlib

theorem solution
    (y θ₁ θ₂ : ℝ) (hy : y < 0)
    (hθ₁ : 0 < θ₁) (hθ : θ₁ ≤ θ₂) :
    (Real.exp (θ₁ * y) - 1) / θ₁ ≤
      (Real.exp (θ₂ * y) - 1) / θ₂ := by
  have hθ₂ : 0 < θ₂ := lt_of_lt_of_le hθ₁ hθ
  have hne₁ : θ₁ ≠ 0 := ne_of_gt hθ₁
  have hne₂ : θ₂ ≠ 0 := ne_of_gt hθ₂
  have hyne : y ≠ 0 := ne_of_lt hy
  have hxy : θ₂ * y ≤ θ₁ * y :=
    mul_le_mul_of_nonpos_right hθ (le_of_lt hy)
  have hne₂y : θ₂ * y ≠ (0 : ℝ) := mul_ne_zero hne₂ hyne
  have hne₁y : θ₁ * y ≠ (0 : ℝ) := mul_ne_zero hne₁ hyne
  have hsec :
      (Real.exp (θ₂ * y) - 1) / (θ₂ * y) ≤
        (Real.exp (θ₁ * y) - 1) / (θ₁ * y) := by
    have h :=
      ConvexOn.secant_mono convexOn_exp
        (a := (0 : ℝ)) (x := θ₂ * y) (y := θ₁ * y)
        (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _)
        hne₂y hne₁y hxy
    simpa only [Real.exp_zero, sub_zero] using h
  have hprod :
      (Real.exp (θ₁ * y) - 1) / (θ₁ * y) * y ≤
        (Real.exp (θ₂ * y) - 1) / (θ₂ * y) * y :=
    mul_le_mul_of_nonpos_right hsec (le_of_lt hy)
  have hformula (θ : ℝ) (hθne : θ ≠ 0) :
      (Real.exp (θ * y) - 1) / (θ * y) * y =
        (Real.exp (θ * y) - 1) / θ := by
    field_simp [hθne, hyne]
  calc
    (Real.exp (θ₁ * y) - 1) / θ₁ =
      (Real.exp (θ₁ * y) - 1) / (θ₁ * y) * y :=
        (hformula θ₁ hne₁).symm
    _ ≤ (Real.exp (θ₂ * y) - 1) / (θ₂ * y) * y := hprod
    _ = (Real.exp (θ₂ * y) - 1) / θ₂ :=
      hformula θ₂ hne₂
