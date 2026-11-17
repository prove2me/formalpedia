-- Prove2me | solution 1 for BranchSpectral.critical_atom_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:18:07.254538+00:00
-- url     : https://prove2.me/submissions/ecc38041-28c6-4c47-bcf4-1824645e52ce

import Mathlib
open MeasureTheory Set Filter Topology


theorem BranchSpectral.critical_atom_nonneg (g t : ℝ) : 0 ≤ (fun (g e t : ℝ) => Real.exp (-(g^2-e^2)*t)*Real.cos (2*e*g*t)) g 0 t := by
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
  positivity

theorem solution (g t : ℝ) : 0 ≤ (fun (g e t : ℝ) => Real.exp (-(g^2-e^2)*t)*Real.cos (2*e*g*t)) g 0 t := by
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
  positivity
