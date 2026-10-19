-- Prove2me | solution 1 for CohnElkies.sinc_quadratic_gap_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/7abbbc0a-2038-4287-82b7-60661d2d5c41

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_sin_le_linear_sub_cubic

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution {x : ℝ}
    (hx0 : 0 ≤ x) (hxhalf : x ≤ (1 / 2 : ℝ)) :
    (4 / 25 : ℝ) * x ^ 2 ≤ 1 - |Real.sinc x| := by
  rcases hx0.eq_or_lt with rfl | hxpos
  · norm_num
  have hxpi : x ≤ Real.pi := by
    linarith [Real.pi_gt_three]
  have hsin0 : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hxpos.le hxpi
  rw [Real.sinc_of_ne_zero hxpos.ne',
    abs_of_nonneg (div_nonneg hsin0 hxpos.le)]
  have hsin := sin_le_linear_sub_cubic hxpos.le hxhalf
  have hfrac : Real.sin x / x ≤ 1 - (4 / 25 : ℝ) * x ^ 2 := by
    apply (div_le_iff₀ hxpos).2
    nlinarith
  linarith
end CohnElkies
