-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn.g_gt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:25:50.579407+00:00
-- url     : https://prove2.me/submissions/e27a1bb0-cf6b-4f21-9071-fef379bf54a1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_b_ge
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_absorb
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
theorem _root_.solution {s q : ℝ} (hs : s ≤ 4 * A * b) (hq : (k * b) ^ 8 ≤ q) : 2 * s + 2 < q := by
  have B := h.toBs
  have hb1 : (1 : ℝ) ≤ b := le_trans (by norm_num) B.b_ge
  have h1 : A * b ≤ 2 * k ^ 2 * b := mul_le_mul_of_nonneg_right h.Ak (by linarith)
  have hk : (64 : ℝ) ≤ k ^ 2 := by nlinarith [h.k8]
  have h2 : 64 * 1 ≤ k ^ 2 * b := mul_le_mul hk hb1 zero_le_one (by linarith)
  have h3 : 18 * k ^ 2 * b ^ 1 ≤ (k * b) ^ 8 :=
    absorb h.k1 B.b_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h4 : b ^ 1 = b := pow_one b
  rw [h4] at h3
  linarith
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn
