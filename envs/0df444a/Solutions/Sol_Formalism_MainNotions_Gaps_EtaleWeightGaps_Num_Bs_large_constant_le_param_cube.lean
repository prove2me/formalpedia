-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs.large_constant_le_param_cube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:43:39.804841+00:00
-- url     : https://prove2.me/submissions/dce5a844-12e8-4b2a-a5b4-410537c20919

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
open Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs
variable {A k b sb PP TO rd : ℝ} (h : Bs A k b sb PP TO rd)
include h
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs
theorem _root_.solution : 10 ^ 100 * A ^ 2 ≤ PP ^ 3 := by
  have hA1 : (1 : ℝ) ≤ A := by linarith [h.forty_eight_le_constant]
  have hA0 : (0 : ℝ) ≤ 10 ^ 60 * A := by linarith
  have h1 : (10 ^ 60 * A) ^ 3 ≤ PP ^ 3 := pow_le_pow_left₀ hA0 h.PPA 3
  have h2 : A ^ 2 ≤ A ^ 3 := pow_le_pow_right₀ hA1 (by norm_num)
  have h3 : (0 : ℝ) ≤ A ^ 2 := sq_nonneg A
  have h4 : (10 ^ 60 * A) ^ 3 = 10 ^ 180 * A ^ 3 := by ring
  rw [h4] at h1
  linarith
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs
