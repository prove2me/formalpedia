-- Prove2me | solution 2 for CohnElkies.saddle_inverse_sqrt_cube_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:02:23.434115+00:00
-- url     : https://prove2.me/submissions/3e902745-a6f6-4f91-af67-8c0acd7f0f19

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
    {q : ℝ} (hq : 0 < q) :
    (Real.sqrt (q / 6) ^ 3)⁻¹ ≤
      1 + (6 / q) ^ 3 := by
  set s := Real.sqrt (q / 6) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hss : s ^ 2 = q / 6 := Real.sq_sqrt (by positivity)
  have h6 : 6 / q = (s ^ 2)⁻¹ := by rw [hss]; field_simp
  rw [h6]
  set u := s⁻¹ with hu
  have hu0 : 0 < u := inv_pos.mpr hs0
  have e1 : (s ^ 3)⁻¹ = u ^ 3 := by rw [hu, inv_pow]
  have e2 : ((s ^ 2)⁻¹) ^ 3 = u ^ 6 := by rw [hu, inv_pow]; ring
  rw [e1, e2]
  nlinarith [sq_nonneg (u ^ 3 - 1), pow_pos hu0 3]

