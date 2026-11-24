-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn.Q_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:42:43.578562+00:00
-- url     : https://prove2.me/submissions/72e3fed7-142b-4059-bb4a-b48f04bf037c

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
theorem _root_.solution : TO + D2 + 2 * r ≤ 3 * TO := by
  have h1 : 0 ≤ D2 * nW := mul_nonneg (by linarith [h.two_le_degree_alt]) (by linarith [h.forty_le_weight_count])
  linarith [h.forty_mul_degree_le_order, h.W, h.one_le_order_alt]
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn
