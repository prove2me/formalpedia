-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs.ATO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:53:07.414014+00:00
-- url     : https://prove2.me/submissions/343b5880-6881-445d-9fb2-38eb049e7e61

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_large_constant_le_param_cube

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
theorem _root_.solution : 10 ^ 100 * (A ^ 2 * TO ^ 2) ≤ sb := by
  have h1 : 10 ^ 100 * A ^ 2 * TO ^ 2 ≤ PP ^ 3 * TO ^ 2 :=
    mul_le_mul_of_nonneg_right h.large_constant_le_param_cube (sq_nonneg TO)
  calc 10 ^ 100 * (A ^ 2 * TO ^ 2) = 10 ^ 100 * A ^ 2 * TO ^ 2 := by ring
    _ ≤ PP ^ 3 * TO ^ 2 := h1
    _ ≤ sb := h.h32
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs
