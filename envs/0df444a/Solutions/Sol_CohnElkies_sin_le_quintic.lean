-- Prove2me | solution 1 for CohnElkies.sin_le_quintic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/51a67861-71f0-41d2-92c4-6bf6ad3a192e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_cos_le_quartic

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 96 := by
  have hpoly : Continuous
      (fun t : ℝ => 1 - t ^ 2 / 2 + t ^ 4 * (5 / 96 : ℝ)) := by
    fun_prop
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hx0
    (Real.continuous_cos.intervalIntegrable 0 x)
    (hpoly.intervalIntegrable 0 x)
    (fun t ht => cos_le_quartic ht.1 (ht.2.trans hx1))
  simp only [integral_cos, Real.sin_zero, sub_zero] at hmono
  have hderiv (t : ℝ) :
      HasDerivAt (fun y : ℝ => y - y ^ 3 / 6 + y ^ 5 / 96)
        (1 - t ^ 2 / 2 + t ^ 4 * (5 / 96 : ℝ)) t := by
    convert! ((hasDerivAt_id t).sub
      (((hasDerivAt_id t).pow 3).div_const 6)).add
      (((hasDerivAt_id t).pow 5).div_const 96) using 1; simp [id]; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hderiv t) (hpoly.intervalIntegrable 0 x)] at hmono
  norm_num at hmono
  exact hmono
end CohnElkies
