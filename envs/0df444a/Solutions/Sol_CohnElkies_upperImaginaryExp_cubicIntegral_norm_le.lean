-- Prove2me | solution 1 for CohnElkies.upperImaginaryExp_cubicIntegral_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/77fe451f-aebb-4c56-965b-ed29c875d2f5

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperImaginaryExp_iteratedDeriv_norm

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {x : ℝ} (hx : 0 ≤ x) :
    ‖∫ t in (0 : ℝ)..x,
        ((x - t) ^ 2 / 2 : ℝ) •
          iteratedDeriv 3 upperImaginaryExp t‖ ≤
      x ^ 3 / 6 := by
  have hcont :
      Continuous (fun t : ℝ => (x - t) ^ 2 / 2) := by
    fun_prop
  have hint :
      IntervalIntegrable
        (fun t : ℝ => (x - t) ^ 2 / 2)
        volume 0 x := hcont.intervalIntegrable 0 x
  have hnorm :
      ‖∫ t in (0 : ℝ)..x,
          ((x - t) ^ 2 / 2 : ℝ) •
            iteratedDeriv 3 upperImaginaryExp t‖ ≤
        ∫ t in (0 : ℝ)..x, (x - t) ^ 2 / 2 := by
    apply intervalIntegral.norm_integral_le_of_norm_le hx
    · filter_upwards [] with t ht
      rw [norm_smul, Real.norm_eq_abs,
        upperImaginaryExp_iteratedDeriv_norm, mul_one,
        abs_of_nonneg (by positivity)]
    · exact hint
  have hprimitive (t : ℝ) :
      HasDerivAt (fun z : ℝ => -(x - z) ^ 3 / 6)
        ((x - t) ^ 2 / 2) t := by
    convert! (((hasDerivAt_const t x).sub
      (hasDerivAt_id t)).pow 3).neg.div_const 6 using 1
    all_goals
      simp [Pi.sub_apply, id]
      ring
  calc
    ‖∫ t in (0 : ℝ)..x,
        ((x - t) ^ 2 / 2 : ℝ) •
          iteratedDeriv 3 upperImaginaryExp t‖ ≤
      ∫ t in (0 : ℝ)..x, (x - t) ^ 2 / 2 := hnorm
    _ = x ^ 3 / 6 := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hprimitive t) hint]
      ring
end CohnElkies
