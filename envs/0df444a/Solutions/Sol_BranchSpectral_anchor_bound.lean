-- Prove2me | solution 1 for BranchSpectral.anchor_bound
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:18:08.079508+00:00
-- url     : https://prove2.me/submissions/698fab31-a1f5-4ce4-9ff4-eca58fb41681

import Mathlib
open MeasureTheory Set Filter Topology


theorem BranchSpectral.anchor_bound (g t : ℝ) (hg : 0 < g) (h100 : g ≤ 100) (ht : 0 < t) :
    Real.exp (-10000*t) ≤ (fun (g e t : ℝ) => Real.exp (-(g^2-e^2)*t)*Real.cos (2*e*g*t)) g 0 t := by
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
  apply Real.exp_le_exp.2
  have : g ^ 2 ≤ 10000 := by nlinarith
  nlinarith

theorem solution (g t : ℝ) (hg : 0 < g) (h100 : g ≤ 100) (ht : 0 < t) :
    Real.exp (-10000*t) ≤ (fun (g e t : ℝ) => Real.exp (-(g^2-e^2)*t)*Real.cos (2*e*g*t)) g 0 t := by
  simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
  apply Real.exp_le_exp.2
  have : g ^ 2 ≤ 10000 := by nlinarith
  nlinarith
