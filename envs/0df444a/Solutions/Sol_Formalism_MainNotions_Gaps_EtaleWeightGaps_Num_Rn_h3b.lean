-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn.h3b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:30.282899+00:00
-- url     : https://prove2.me/submissions/77db6c7d-78bd-47f8-9a9b-e3b8b33025fd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_sb_le_b
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_b_ge
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_TO_le_sb
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_PP_le_sb
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_rd_pow_le
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_absorb
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Rn_b_pos
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Rn_PP_pos
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Rn_d_sq
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Rn_k1
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Rn_r_le

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
    TO * (1250 * r) * rd ^ 2 * PP * d ^ 2 ≤ q := by
  have B := h.toBs
  have hb0 := h.b_pos.le
  have hT : TO ≤ b := le_trans B.TO_le_sb B.sb_le_b
  have hrd : rd ^ 2 ≤ b := le_trans (B.rd_pow_le (by norm_num)) B.sb_le_b
  have hP : PP ≤ b := le_trans B.PP_le_sb B.sb_le_b
  have hd2 := h.d_sq hd0 hd
  have hk2 : (0 : ℝ) ≤ 1250 * k ^ 2 := by positivity
  have s1 : TO * (1250 * r) ≤ b * (1250 * k ^ 2) :=
    mul_le_mul hT (by linarith [h.r_le]) (by linarith [h.r6]) hb0
  have n1 : 0 ≤ b * (1250 * k ^ 2) := mul_nonneg hb0 hk2
  have s2 : TO * (1250 * r) * rd ^ 2 ≤ b * (1250 * k ^ 2) * b := mul_le_mul s1 hrd (sq_nonneg rd) n1
  have n2 : 0 ≤ b * (1250 * k ^ 2) * b := mul_nonneg n1 hb0
  have s3 : TO * (1250 * r) * rd ^ 2 * PP ≤ b * (1250 * k ^ 2) * b * b := mul_le_mul s2 hP h.PP_pos.le n2
  have n3 : 0 ≤ b * (1250 * k ^ 2) * b * b := mul_nonneg n2 hb0
  have s4 : TO * (1250 * r) * rd ^ 2 * PP * d ^ 2 ≤ b * (1250 * k ^ 2) * b * b * (16 * k ^ 4 * b ^ 2) :=
    mul_le_mul s3 hd2 (sq_nonneg d) n3
  have s5 : 20000 * k ^ 6 * b ^ 5 ≤ (k * b) ^ 8 :=
    absorb h.k1 B.b_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s6 : b * (1250 * k ^ 2) * b * b * (16 * k ^ 4 * b ^ 2) = 20000 * k ^ 6 * b ^ 5 := by ring
  linarith
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn
