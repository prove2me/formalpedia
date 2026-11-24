-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn.h3e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:30.997562+00:00
-- url     : https://prove2.me/submissions/a3da1eb8-92e7-4c45-8400-edbb1a586ab1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_sb_le_b
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_b_ge
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_PP_le_sb
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_rd_pow_le
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_absorb
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Rn_b_pos
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
theorem _root_.solution {d q fm : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 2 * A * b) (hq : (k * b) ^ 8 ≤ q) (hf0 : 0 ≤ fm) (hf : fm ≤ k ^ 4) :
    2 * (fm * (rd ^ 2) ^ 2 * (rd ^ 2 * PP * d ^ 2)) ≤ q := by
  have B := h.toBs
  have hb0 := h.b_pos.le
  have hrd4 : (rd ^ 2) ^ 2 ≤ b := by
    have : (rd ^ 2) ^ 2 = rd ^ 4 := by ring
    rw [this]; exact le_trans (B.rd_pow_le (by norm_num)) B.sb_le_b
  have hrd : rd ^ 2 ≤ b := le_trans (B.rd_pow_le (by norm_num)) B.sb_le_b
  have hP : PP ≤ b := le_trans B.PP_le_sb B.sb_le_b
  have hd2 := h.d_sq hd0 hd
  have hPP0 := h.PP_pos.le
  have t1 : fm * (rd ^ 2) ^ 2 ≤ k ^ 4 * b := mul_le_mul hf hrd4 (by positivity) (by positivity)
  have t2 : rd ^ 2 * PP ≤ b * b := mul_le_mul hrd hP hPP0 hb0
  have t3 : rd ^ 2 * PP * d ^ 2 ≤ b * b * (16 * k ^ 4 * b ^ 2) :=
    mul_le_mul t2 hd2 (sq_nonneg d) (mul_nonneg hb0 hb0)
  have t4 : fm * (rd ^ 2) ^ 2 * (rd ^ 2 * PP * d ^ 2) ≤ k ^ 4 * b * (b * b * (16 * k ^ 4 * b ^ 2)) :=
    mul_le_mul t1 t3 (mul_nonneg (mul_nonneg (sq_nonneg rd) hPP0) (sq_nonneg d)) (mul_nonneg (by positivity) hb0)
  have t5 : 32 * k ^ 8 * b ^ 5 ≤ (k * b) ^ 8 :=
    absorb h.k1 B.b_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t6 : 2 * (k ^ 4 * b * (b * b * (16 * k ^ 4 * b ^ 2))) = 32 * k ^ 8 * b ^ 5 := by ring
  linarith
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn
