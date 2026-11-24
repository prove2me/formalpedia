-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn.k1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:42:34.723607+00:00
-- url     : https://prove2.me/submissions/43ac0a06-ce76-4903-ae00-93cbbc8c048c

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
theorem _root_.solution : 1 ≤ k := by linarith [h.k8]
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn
