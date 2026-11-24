-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs.param_cube_le_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:58:54.915797+00:00
-- url     : https://prove2.me/submissions/a4f5b3a3-e0f2-47b1-bfc6-ea313d431004

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_PP_ge

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
theorem _root_.solution : PP ^ 3 ≤ sb := by
  have hP : (0 : ℝ) ≤ PP := le_trans (by norm_num) h.PP_ge
  have hT : (1 : ℝ) ≤ TO ^ 2 := by nlinarith [h.one_le_order_alt]
  have h1 : PP ^ 3 * 1 ≤ PP ^ 3 * TO ^ 2 := mul_le_mul_of_nonneg_left hT (pow_nonneg hP 3)
  linarith [h.h32]
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs
