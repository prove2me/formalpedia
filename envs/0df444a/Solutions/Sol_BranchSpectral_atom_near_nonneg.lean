-- Prove2me | solution 1 for BranchSpectral.atom_near_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:18:08.93754+00:00
-- url     : https://prove2.me/submissions/a902811f-f36f-4997-a271-4848729c5eb4

import Mathlib
open MeasureTheory Set Filter Topology


theorem BranchSpectral.atom_near_nonneg (g e t : ℝ) (hg : 0 < g)
    (he : |e| ≤ 1/2) (ht : 0 < t) (hnear : g ≤ t⁻¹) :
    0 ≤ (fun (g e t : ℝ) => Real.exp (-(g^2-e^2)*t)*Real.cos (2*e*g*t)) g e t := by
  simp only
  apply mul_nonneg (Real.exp_pos _).le
  have hgt : g * t ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hnear ht.le
    rwa [inv_mul_cancel₀ ht.ne'] at this
  have hgt0 : 0 ≤ g * t := by positivity
  have habs : |2 * e * g * t| ≤ 1 := by
    rw [show 2 * e * g * t = (2 * e) * (g * t) by ring, abs_mul, abs_of_nonneg hgt0, abs_mul]
    have : |(2:ℝ)| * |e| ≤ 1 := by rw [abs_two]; linarith
    calc |2| * |e| * (g * t) ≤ 1 * 1 := by
          apply mul_le_mul this hgt hgt0 (by norm_num)
      _ = 1 := by norm_num
  apply Real.cos_nonneg_of_mem_Icc
  rw [abs_le] at habs
  constructor <;> linarith [Real.pi_gt_three]

theorem solution (g e t : ℝ) (hg : 0 < g)
    (he : |e| ≤ 1/2) (ht : 0 < t) (hnear : g ≤ t⁻¹) :
    0 ≤ (fun (g e t : ℝ) => Real.exp (-(g^2-e^2)*t)*Real.cos (2*e*g*t)) g e t := by
  simp only
  apply mul_nonneg (Real.exp_pos _).le
  have hgt : g * t ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hnear ht.le
    rwa [inv_mul_cancel₀ ht.ne'] at this
  have hgt0 : 0 ≤ g * t := by positivity
  have habs : |2 * e * g * t| ≤ 1 := by
    rw [show 2 * e * g * t = (2 * e) * (g * t) by ring, abs_mul, abs_of_nonneg hgt0, abs_mul]
    have : |(2:ℝ)| * |e| ≤ 1 := by rw [abs_two]; linarith
    calc |2| * |e| * (g * t) ≤ 1 * 1 := by
          apply mul_le_mul this hgt hgt0 (by norm_num)
      _ = 1 := by norm_num
  apply Real.cos_nonneg_of_mem_Icc
  rw [abs_le] at habs
  constructor <;> linarith [Real.pi_gt_three]
