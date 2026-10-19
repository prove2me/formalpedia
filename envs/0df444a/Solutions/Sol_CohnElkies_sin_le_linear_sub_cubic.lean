-- Prove2me | solution 1 for CohnElkies.sin_le_linear_sub_cubic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/413fff0e-c36a-49e2-9034-3d28cb60a97c

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_sin_le_quintic

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
    Real.sin x ≤ x - (4 / 25 : ℝ) * x ^ 3 := by
  have hx1 : x ≤ (1 : ℝ) := by linarith
  have hsin := sin_le_quintic hx0 hx1
  have hsq : x ^ 2 ≤ (1 / 4 : ℝ) := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hxhalf)]
  have hcub : 0 ≤ x ^ 3 := pow_nonneg hx0 _
  have hfifth : x ^ 5 ≤ x ^ 3 / 4 := by
    have hprod := mul_nonneg hcub (sub_nonneg.mpr hsq)
    nlinarith [show x ^ 5 = x ^ 3 * x ^ 2 by ring]
  nlinarith
end CohnElkies
