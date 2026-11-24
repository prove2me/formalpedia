-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn.h3f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:38:47.173582+00:00
-- url     : https://prove2.me/submissions/c75ad668-7d06-4f88-8821-fea4e4008506

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_sb_le_b
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_b_ge
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_TO_le_sb
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_absorb
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Rn_d_le
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
theorem _root_.solution {d q : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ 2 * A * b) (hq : (k * b) ^ 8 ≤ q) : (D2 + 2) * d ≤ q - 2 := by
  have B := h.toBs
  have hb1 : (1 : ℝ) ≤ b := le_trans (by norm_num) B.b_ge
  have hT : TO ≤ b := le_trans B.TO_le_sb B.sb_le_b
  have h1 : D2 + 2 ≤ 2 * b := by linarith [h.forty_mul_degree_le_order, h.one_le_order_alt, B.b_ge]
  have h2 := h.d_le hd
  have h3 : (D2 + 2) * d ≤ 2 * b * (4 * k ^ 2 * b) := mul_le_mul h1 h2 hd0 (by linarith)
  have hk1 : (1 : ℝ) ≤ k ^ 2 := by nlinarith [h.k1]
  have hb2 : (1 : ℝ) ≤ b ^ 2 := by nlinarith
  have h4 : 1 * 1 ≤ k ^ 2 * b ^ 2 := mul_le_mul hk1 hb2 zero_le_one (by linarith)
  have h5 : 10 * k ^ 2 * b ^ 2 ≤ (k * b) ^ 8 :=
    absorb h.k1 B.b_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  nlinarith
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn
