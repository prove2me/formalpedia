-- Prove2me | solution 1 for ConnesGreen.smallSupportCost_positive
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T04:25:48.304229+00:00
-- url     : https://prove2.me/submissions/9c0f471e-ada4-4020-be0e-190ca8fce4b7

import Theorems.Thm_ConnesGreen_gammaBracket_zero_le
import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_canonical_model
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.ConnesNative Set
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace ConnesGreen
theorem positiveGammaCutoff_positive : 0 < positiveGammaCutoff := by
  unfold positiveGammaCutoff
  positivity

theorem _root_.solution : 0 < smallSupportCost := by
  have hγ : 0 ≤ Zeta23.EF.gammaBracket positiveGammaCutoff - Zeta23.EF.gammaBracket 0 := by
    apply sub_nonneg.mpr
    simpa [Zeta23.EF.gammaBracket] using gammaBracket_zero_le positiveGammaCutoff
  have hB := positiveGammaCutoff_positive
  unfold smallSupportCost
  positivity
end ConnesGreen
