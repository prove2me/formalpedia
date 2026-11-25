-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn.kl_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:20:48.091705+00:00
-- url     : https://prove2.me/submissions/081b90db-654c-4809-a8d7-2d1705944362

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube
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
theorem _root_.solution : b ≤ D2 * nW + 2 * r + (TO + D2) * q0 := by
  have hq := h.modulus_pos_alt
  have h1 : 0 ≤ D2 * nW := mul_nonneg (by linarith [h.two_le_degree_alt]) (by linarith [h.forty_le_weight_count])
  have h2 : 0 ≤ D2 * q0 := mul_nonneg (by linarith [h.two_le_degree_alt]) hq.le
  linarith [h.q0lo, h.r6]
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn
