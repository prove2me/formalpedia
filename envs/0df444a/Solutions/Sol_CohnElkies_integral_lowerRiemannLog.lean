-- Prove2me | solution 1 for CohnElkies.integral_lowerRiemannLog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/bb40dd54-ff8b-4e84-b53d-76905f22bdcc

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerRiemannLog_monotoneOn
import Theorems.Thm_CohnElkies_lowerRiemannLogPrimitive_hasDerivAt

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    {T : ℝ} (hT : T ≠ 0) :
    -(∫ x in (0 : ℝ)..1, lowerRiemannLog T x) =
      1 + lowerEndpointPhase T := by
  have hmono : MonotoneOn (lowerRiemannLog T)
      (Icc (0 : ℝ) 1) :=
    (lowerRiemannLog_monotoneOn hT).mono
      (by intro x hx; exact hx.1)
  have hmono' : MonotoneOn (lowerRiemannLog T)
      ([[0, 1]] : Set ℝ) := by
    simpa using! hmono
  have hint :
      IntervalIntegrable (lowerRiemannLog T) volume (0 : ℝ) 1 :=
    hmono'.intervalIntegrable
  have hFTC :
      (∫ x in (0 : ℝ)..1, lowerRiemannLog T x) =
        lowerRiemannLogPrimitive T 1 -
          lowerRiemannLogPrimitive T 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => lowerRiemannLogPrimitive_hasDerivAt hT x) hint
  have ha : 0 < |T| / 2 := half_pos (abs_pos.mpr hT)
  have hatan :
      Real.arctan (1 / (|T| / 2)) =
        Real.pi / 2 - Real.arctan (|T| / 2) := by
    simpa [one_div] using! Real.arctan_inv_of_pos ha
  rw [hFTC]
  unfold lowerRiemannLogPrimitive lowerEndpointPhase
  simp only [one_pow, zero_pow (by norm_num : 2 ≠ 0), zero_add,
    zero_div, zero_mul, sub_zero, Real.arctan_zero]
  rw [hatan]
  ring
end CohnElkies
