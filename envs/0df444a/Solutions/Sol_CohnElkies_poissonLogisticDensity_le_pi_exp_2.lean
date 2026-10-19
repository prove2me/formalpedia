-- Prove2me | solution 2 for CohnElkies.poissonLogisticDensity_le_pi_exp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:01:55.417782+00:00
-- url     : https://prove2.me/submissions/fb80ada0-f041-45ee-8a00-cdd150db9107

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology


theorem solution (u : ℝ) :
    poissonLogisticDensity u ≤
      Real.pi * Real.exp (-Real.pi * |u|) := by
  unfold poissonLogisticDensity
  have hE := Real.exp_pos (Real.pi * u)
  have hp := Real.pi_pos
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu, show -Real.pi * u = -(Real.pi * u) by ring, Real.exp_neg,
      div_le_iff₀ (by positivity)]
    have key : (Real.exp (Real.pi * u))⁻¹ * (1 + Real.exp (Real.pi * u)) ^ 2 =
        (Real.exp (Real.pi * u))⁻¹ + 2 + Real.exp (Real.pi * u) := by
      field_simp; ring
    have hi := inv_pos.2 hE
    nlinarith
  · rw [abs_of_neg hu, show -Real.pi * -u = Real.pi * u by ring, div_le_iff₀ (by positivity)]
    nlinarith [mul_pos (mul_pos hp hE) hE, mul_pos (mul_pos hp hE) (mul_pos hE hE)]

