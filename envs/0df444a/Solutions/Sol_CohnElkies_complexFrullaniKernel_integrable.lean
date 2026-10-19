-- Prove2me | solution 1 for CohnElkies.complexFrullaniKernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/dd6c4f30-c1a5-49c4-85b2-f6b7c2234da6

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_intervalIntegral_complexLaplaceSegment
import Theorems.Thm_CohnElkies_complexFrullaniParameter_integrable

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
    {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    IntegrableOn (complexFrullaniKernel z w) (Ioi 0) := by
  have hproduct :=
    (complexFrullaniParameter_integrable hz hw).integral_prod_right
  apply hproduct.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change
    (∫ s in Set.uIoc (0 : ℝ) 1,
      (w - z) *
        Complex.exp
          (-complexFrullaniSegment z w s * (x : ℂ))) =
      complexFrullaniKernel z w x
  rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    ← intervalIntegral.integral_of_le
      (show (0 : ℝ) ≤ 1 by norm_num)]
  exact intervalIntegral_complexLaplaceSegment z w (ne_of_gt hx)
end CohnElkies
