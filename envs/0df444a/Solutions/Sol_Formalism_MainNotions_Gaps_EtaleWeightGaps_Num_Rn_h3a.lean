-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn.h3a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:29.384517+00:00
-- url     : https://prove2.me/submissions/1012f881-27f3-4175-aa2f-8eb07af9860e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_b_ge
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_param_cube_le_bound
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_absorb
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Rn_sb_pos
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Rn_PP_pos
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Rn_d_sq
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Rn_k1

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
theorem _root_.solution {d q : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 2 * A * b) (hq : (k * b) ^ 8 ≤ q) :
    (rd ^ 2) ^ 4 * PP ^ 3 * d ^ 2 ≤ q := by
  have hsb0 := h.sb_pos.le
  have e1 : (rd ^ 2) ^ 4 ≤ sb := by
    have : (rd ^ 2) ^ 4 = rd ^ 8 := by ring
    rw [this]; exact h.rd8
  have e2 : PP ^ 3 ≤ sb := h.toBs.param_cube_le_bound
  have e3 := h.d_sq hd0 hd
  have s1 : (rd ^ 2) ^ 4 * PP ^ 3 ≤ sb * sb := mul_le_mul e1 e2 (pow_nonneg h.PP_pos.le 3) hsb0
  have s2 : (rd ^ 2) ^ 4 * PP ^ 3 * d ^ 2 ≤ sb * sb * (16 * k ^ 4 * b ^ 2) :=
    mul_le_mul s1 e3 (sq_nonneg d) (mul_nonneg hsb0 hsb0)
  have s3 : sb * sb * (16 * k ^ 4 * b ^ 2) = 16 * k ^ 4 * b ^ 3 := by
    rw [h.sb_sq]; ring
  have s4 : 16 * k ^ 4 * b ^ 3 ≤ (k * b) ^ 8 :=
    absorb h.k1 h.toBs.b_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  linarith
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn
