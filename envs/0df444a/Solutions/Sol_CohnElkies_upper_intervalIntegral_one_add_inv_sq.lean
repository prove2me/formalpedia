-- Prove2me | solution 1 for CohnElkies.upper_intervalIntegral_one_add_inv_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/1d56411f-24e9-4c22-854c-321eef9fcb70

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, 1 + (x ^ 2)⁻¹) =
      b - a + a⁻¹ - b⁻¹ := by
  have hcont :
      ContinuousOn (fun x : ℝ => 1 + (x ^ 2)⁻¹)
        (Set.Icc a b) := by
    apply continuousOn_const.add
      ((continuous_id.pow 2).continuousOn.inv₀ ?_)
    intro x hx
    have hxpos : 0 < x := ha.trans_le hx.1
    exact (sq_pos_of_pos hxpos).ne'
  have hderiv (x : ℝ) (hx : x ∈ Set.Icc a b) :
      HasDerivAt (fun y : ℝ => y - y⁻¹)
        (1 + (x ^ 2)⁻¹) x := by
    have hxpos : 0 < x := ha.trans_le hx.1
    convert! (hasDerivAt_id x).sub
      (hasDerivAt_inv hxpos.ne') using 1; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hderiv x
      (by simpa [Set.uIcc_of_le hab] using! hx))
    (hcont.intervalIntegrable_of_Icc hab)]
  ring
end CohnElkies
