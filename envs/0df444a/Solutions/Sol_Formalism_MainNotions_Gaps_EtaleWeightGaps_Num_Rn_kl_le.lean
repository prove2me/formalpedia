-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn.kl_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:33:45.955803+00:00
-- url     : https://prove2.me/submissions/01f9f433-6bd1-4ed1-bbab-70b4a92a1acb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_b_ge
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Rn_modulus_pos_alt

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
theorem _root_.solution : D2 * nW + 2 * r + (TO + D2) * q0 ≤ 3 * TO + 2 * b := by
  have hq := h.modulus_pos_alt
  have h40 : 40 * D2 * q0 ≤ TO * q0 := mul_le_mul_of_nonneg_right h.forty_mul_degree_le_order hq.le
  have hb : (0 : ℝ) ≤ b := le_trans (by norm_num) h.toBs.b_ge
  linarith [h.W, h.q0hi, h.one_le_order_alt]
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn
