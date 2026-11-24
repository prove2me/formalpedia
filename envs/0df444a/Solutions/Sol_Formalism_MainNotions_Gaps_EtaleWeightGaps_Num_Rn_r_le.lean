-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn.r_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:43:41.847122+00:00
-- url     : https://prove2.me/submissions/8bcea024-391e-4d1c-b754-36a2e5a2abe7

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
open Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn
variable {A k b sb PP TO rd r D2 nW nP q0 : ℝ} (h : Rn A k b sb PP TO rd r D2 nW nP q0)
include h
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn
theorem _root_.solution : r ≤ k ^ 2 := by linarith [sq_nonneg k, h.rA, h.Ak]
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn
