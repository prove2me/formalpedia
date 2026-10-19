-- Prove2me | solution 1 for CohnElkies.saddleSecondBranch_linearWeightedCoefficient_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/b2681ea8-16a4-4177-bc71-6f00f5c0afd3

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
namespace CohnElkies
theorem _root_.solution
    {a η C : ℝ}
    (ha : 0 < a)
    (hη : 1 ≤ η)
    (hC : 0 < C)
    (hrate : 1 / a ≤ C) :
    2 * max (1 : ℝ) (((a / 6) ^ 3)⁻¹) *
        (2 / (a / 2)) ≤
      (8 * C * (1 + (6 * C) ^ 3)) * η ^ 4 := by
  have hηfour : 1 ≤ η ^ 4 := by
    simpa using!
      (pow_le_pow_left₀
        (show (0 : ℝ) ≤ 1 by norm_num) hη 4)
  have hidentity :
      ((a / 6) ^ 3)⁻¹ = (6 / a) ^ 3 := by
    field_simp [ha.ne']
  have hbase : 6 / a ≤ 6 * C := by
    calc
      6 / a = 6 * (1 / a) := by ring
      _ ≤ 6 * C := by gcongr
  have hmax :
      max (1 : ℝ) (((a / 6) ^ 3)⁻¹) ≤
        1 + (6 * C) ^ 3 := by
    rw [hidentity]
    apply max_le
    · have : 0 ≤ (6 * C) ^ 3 := by positivity
      linarith
    · have hcubes : (6 / a) ^ 3 ≤ (6 * C) ^ 3 := by
        gcongr
      linarith
  have hlinear : 2 / (a / 2) ≤ 4 * C := by
    calc
      2 / (a / 2) = 4 * (1 / a) := by
        field_simp [ha.ne']; ring
      _ ≤ 4 * C := by gcongr
  calc
    2 * max (1 : ℝ) (((a / 6) ^ 3)⁻¹) *
        (2 / (a / 2)) ≤
      2 * (1 + (6 * C) ^ 3) * (4 * C) := by
        gcongr
    _ ≤ (8 * C * (1 + (6 * C) ^ 3)) * η ^ 4 := by
      have hcoefficient :
          0 ≤ 8 * C * (1 + (6 * C) ^ 3) := by
        positivity
      nlinarith [mul_le_mul_of_nonneg_left
        hηfour hcoefficient]
end CohnElkies
