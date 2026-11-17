-- Prove2me | solution 1 for BranchSpectral.atom_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:18:09.88762+00:00
-- url     : https://prove2.me/submissions/e9aeb9b5-7bc9-4dea-9d05-f449c0f569c5

import Mathlib
open MeasureTheory Set Filter Topology


theorem BranchSpectral.atom_abs_bound (g e t : ℝ) (he : |e| ≤ 1/2) (ht : 0 < t) :
    |(fun (g e t : ℝ) => Real.exp (-(g^2-e^2)*t)*Real.cos (2*e*g*t)) g e t| ≤ Real.exp (t/4)*(fun (g t : ℝ) => Real.exp (-g^2*t)) g t := by
  simp only
  rw [abs_mul, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  calc Real.exp (-(g ^ 2 - e ^ 2) * t) * |Real.cos (2 * e * g * t)|
      ≤ Real.exp (-(g ^ 2 - e ^ 2) * t) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
    _ ≤ Real.exp (t / 4 + -g ^ 2 * t) := by
        rw [mul_one]
        apply Real.exp_le_exp.2
        have : e ^ 2 ≤ 1 / 4 := by
          have h0 : 0 ≤ |e| := abs_nonneg e
          have : |e| ^ 2 ≤ (1/2) ^ 2 := pow_le_pow_left₀ h0 he 2
          rw [sq_abs] at this; linarith
        nlinarith

theorem solution (g e t : ℝ) (he : |e| ≤ 1/2) (ht : 0 < t) :
    |(fun (g e t : ℝ) => Real.exp (-(g^2-e^2)*t)*Real.cos (2*e*g*t)) g e t| ≤ Real.exp (t/4)*(fun (g t : ℝ) => Real.exp (-g^2*t)) g t := by
  simp only
  rw [abs_mul, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  calc Real.exp (-(g ^ 2 - e ^ 2) * t) * |Real.cos (2 * e * g * t)|
      ≤ Real.exp (-(g ^ 2 - e ^ 2) * t) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
    _ ≤ Real.exp (t / 4 + -g ^ 2 * t) := by
        rw [mul_one]
        apply Real.exp_le_exp.2
        have : e ^ 2 ≤ 1 / 4 := by
          have h0 : 0 ≤ |e| := abs_nonneg e
          have : |e| ^ 2 ≤ (1/2) ^ 2 := pow_le_pow_left₀ h0 he 2
          rw [sq_abs] at this; linarith
        nlinarith
