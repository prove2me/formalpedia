-- Prove2me | solution 2 for CohnElkies.saddleSecondBranch_linearWeightedCoefficient_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:14.577734+00:00
-- url     : https://prove2.me/submissions/898a8d62-e9cc-4d55-bef2-e75765e35291

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology


theorem solution
    {a η C : ℝ}
    (ha : 0 < a)
    (hη : 1 ≤ η)
    (hC : 0 < C)
    (hrate : 1 / a ≤ C) :
    2 * max (1 : ℝ) (((a / 6) ^ 3)⁻¹) *
        (2 / (a / 2)) ≤
      (8 * C * (1 + (6 * C) ^ 3)) * η ^ 4 := by
  have hinv : 1 / a ≤ C := hrate
  have hC0 : 0 ≤ C := hC.le
  have hm : max (1 : ℝ) (((a / 6) ^ 3)⁻¹) ≤ 1 + (6 * C) ^ 3 := by
    apply max_le
    · have : 0 ≤ (6 * C) ^ 3 := by positivity
      linarith
    · have h6 : ((a / 6) ^ 3)⁻¹ = (6 * (1 / a)) ^ 3 := by field_simp
      rw [h6]
      have : (6 * (1 / a)) ^ 3 ≤ (6 * C) ^ 3 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 3
      linarith
  have h2 : 2 / (a / 2) = 4 * (1 / a) := by field_simp; ring
  have hη4 : 1 ≤ η ^ 4 := one_le_pow₀ hη
  have hmpos : 0 ≤ max (1 : ℝ) (((a / 6) ^ 3)⁻¹) := le_trans zero_le_one (le_max_left _ _)
  rw [h2]
  have hA : 0 ≤ 8 * C * (1 + (6 * C) ^ 3) := by positivity
  calc 2 * max (1 : ℝ) (((a / 6) ^ 3)⁻¹) * (4 * (1 / a))
      ≤ 2 * (1 + (6 * C) ^ 3) * (4 * C) := by
        apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    _ = 8 * C * (1 + (6 * C) ^ 3) * 1 := by ring
    _ ≤ 8 * C * (1 + (6 * C) ^ 3) * η ^ 4 := mul_le_mul_of_nonneg_left hη4 hA

