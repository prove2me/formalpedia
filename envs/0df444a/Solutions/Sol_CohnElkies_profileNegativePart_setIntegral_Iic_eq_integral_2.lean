-- Prove2me | solution 2 for CohnElkies.profileNegativePart_setIntegral_Iic_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:19:26.567446+00:00
-- url     : https://prove2.me/submissions/76f9b7fc-a96c-4ade-b0ce-73ca431c283e

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology


theorem solution {φ : ℝ → ℝ}
    (hsign : ∀ v : ℝ, 0 ≤ v → 0 ≤ φ v) :
    (∫ v in Iic (0 : ℝ), profileNegativePart φ v) =
      ∫ v : ℝ, profileNegativePart φ v := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro v hv
  simp only [Set.mem_Iic, not_le] at hv
  unfold profileNegativePart
  have := hsign v hv.le
  simp only [max_eq_right (by linarith : -φ v ≤ 0)]

