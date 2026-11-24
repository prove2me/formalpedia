-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs.sb_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:01:30.128258+00:00
-- url     : https://prove2.me/submissions/2326be5d-94e0-4e75-8010-fdbdf0536e6b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_ATO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.EtaleWeightGaps.Num
open Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs
variable {A k b sb PP TO rd : ℝ} (h : Bs A k b sb PP TO rd)
include h
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs
theorem _root_.solution : (10 : ℝ) ^ 100 ≤ sb := by
  have hA1 : (1 : ℝ) ≤ A := by linarith [h.forty_eight_le_constant]
  have hT1 := h.one_le_order_alt
  have hAT : (1 : ℝ) ≤ A * TO := by nlinarith
  have hQ : (1 : ℝ) ≤ A ^ 2 * TO ^ 2 := by nlinarith
  have := h.ATO
  nlinarith
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs
