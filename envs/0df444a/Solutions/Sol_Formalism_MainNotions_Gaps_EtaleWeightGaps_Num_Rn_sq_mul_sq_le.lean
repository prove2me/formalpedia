-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn.sq_mul_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:25:09.37748+00:00
-- url     : https://prove2.me/submissions/67c2c2dc-918e-4aa2-9682-ee82fa8c9cfd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_ATOb

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
theorem _root_.solution : A ^ 2 * TO ^ 2 ≤ b := by
  have h1 := h.toBs.ATOb
  have h2 : 0 ≤ A ^ 2 * TO ^ 2 := by positivity
  linarith
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn
