-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn.d_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:38:58.326802+00:00
-- url     : https://prove2.me/submissions/9e5165f4-1463-44cf-ae7c-d2e7f22bb9e5

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Rn_d_le

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
theorem _root_.solution {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 2 * A * b) : d ^ 2 ≤ 16 * k ^ 4 * b ^ 2 := by
  have h1 := pow_le_pow_left₀ hd0 (h.d_le hd) 2
  calc d ^ 2 ≤ (4 * k ^ 2 * b) ^ 2 := h1
    _ = 16 * k ^ 4 * b ^ 2 := by ring
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn
