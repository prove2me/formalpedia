-- Prove2me | solution 1 for ConnesGreen.positiveSupportRadius_positive
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T04:28:13.943233+00:00
-- url     : https://prove2.me/submissions/e67e98c3-4ec4-4fdb-81a5-9eb95b3ce4e4

import Theorems.Thm_ConnesGreen_smallSupportCost_positive
import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_canonical_model
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.ConnesNative Set
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace ConnesGreen
theorem _root_.solution : 0 < positiveSupportRadius := by
  unfold positiveSupportRadius
  have hc := smallSupportCost_positive
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity
end ConnesGreen
