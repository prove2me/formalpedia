-- Prove2me | solution 1 for CohnElkies.profileNegativePart_setIntegral_Iic_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/eb8253b2-0af3-48ec-b4b0-a53c5736b04c

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
namespace CohnElkies
theorem _root_.solution {φ : ℝ → ℝ}
    (hsign : ∀ v : ℝ, 0 ≤ v → 0 ≤ φ v) :
    (∫ v in Iic (0 : ℝ), profileNegativePart φ v) =
      ∫ v : ℝ, profileNegativePart φ v := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro v hv
  have hvpos : 0 < v := by simpa using! hv
  unfold profileNegativePart
  exact max_eq_right (by linarith [hsign v hvpos.le])
end CohnElkies
