-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs.ATOb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:18:02.08347+00:00
-- url     : https://prove2.me/submissions/c3c66abb-3e94-4b0a-8221-baf2bc4eac58

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_ATO
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_sb_le_b

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
theorem _root_.solution : 10 ^ 100 * (A ^ 2 * TO ^ 2) ≤ b := le_trans h.ATO h.sb_le_b
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs
