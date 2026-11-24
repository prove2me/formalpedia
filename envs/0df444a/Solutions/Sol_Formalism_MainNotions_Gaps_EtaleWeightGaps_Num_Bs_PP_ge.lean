-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs.PP_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:42:35.452895+00:00
-- url     : https://prove2.me/submissions/b4ae2d5c-42bb-4938-9ce4-9b4898e741e9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube

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
theorem _root_.solution : (10 : ℝ) ^ 60 ≤ PP := by
  have h1 := h.PPA
  have h2 := h.forty_eight_le_constant
  linarith
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs
