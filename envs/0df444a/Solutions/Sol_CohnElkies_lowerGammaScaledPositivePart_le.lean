-- Prove2me | solution 1 for CohnElkies.lowerGammaScaledPositivePart_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/8f967b20-62fe-431a-b880-7cd3dd3e00f7

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerCoth_log_nonneg
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_dimension_scaled_log_tail_uniform

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
    {d : ℕ} (hd : 2 ≤ d) {c Y : ℝ}
    (hc : 0 < c) (hY : Y ≠ 0) :
    lowerGammaScaledPositivePart d c Y ≤
      ((d : ℝ) / 2) *
        max (Real.log (4 * Real.pi * c ^ 2 / |Y|)) 0 +
        (1 / 2 : ℝ) *
          Real.log (lowerCoth (Real.pi * |Y| / 2)) := by
  have hℓ : 0 ≤ (d : ℝ) / 2 := by positivity
  have hcoth : 0 ≤ Real.log
      (lowerCoth (Real.pi * |Y| / 2)) :=
    lowerCoth_log_nonneg (by positivity)
  have hlog :
      ((d : ℝ) / 2) *
          Real.log (4 * Real.pi * c ^ 2 / |Y|) ≤
        ((d : ℝ) / 2) *
          max (Real.log (4 * Real.pi * c ^ 2 / |Y|)) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hℓ
  have htail := lowerGammaBoundaryLog_dimension_scaled_log_tail_uniform
    hd hc hY
  unfold lowerGammaScaledPositivePart
  apply max_le
  · linarith
  · positivity
end CohnElkies
