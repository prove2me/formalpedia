-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs.b_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:18:13.767221+00:00
-- url     : https://prove2.me/submissions/623bdbd6-e60d-49d3-8e40-7f5ad3de751d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_sb_ge
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
theorem _root_.solution : (10 : ℝ) ^ 100 ≤ b := le_trans h.sb_ge h.sb_le_b
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs
