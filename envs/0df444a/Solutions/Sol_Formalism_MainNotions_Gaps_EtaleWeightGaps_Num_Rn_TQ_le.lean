-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn.TQ_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:43:40.893496+00:00
-- url     : https://prove2.me/submissions/d8bc08df-a9ef-4230-ac29-c5bee4cbc3e3

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
theorem _root_.solution : (TO + D2) * (TO + D2 + 2 * r) ≤ 6 * TO ^ 2 := by
  have hT1 := h.one_le_order_alt
  have hD2 := h.two_le_degree_alt
  have hr6 := h.r6
  have hDW : D2 * 1 ≤ D2 * nW := mul_le_mul_of_nonneg_left (by linarith [h.forty_le_weight_count]) (by linarith)
  have hQ : TO + D2 + 2 * r ≤ 3 * TO := by linarith [h.W, h.forty_mul_degree_le_order]
  have hD : TO + D2 ≤ 2 * TO := by linarith [h.forty_mul_degree_le_order]
  calc (TO + D2) * (TO + D2 + 2 * r) ≤ (2 * TO) * (3 * TO) :=
        mul_le_mul hD hQ (by linarith) (by linarith)
    _ = 6 * TO ^ 2 := by ring
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn
