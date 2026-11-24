-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn.dL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:33:45.175477+00:00
-- url     : https://prove2.me/submissions/7c907a1f-d495-4a0f-91d9-c52391bf9a37

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_ATOb
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Rn_modulus_pos_alt
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Rn_Q_le
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Rn_b_le_Ab

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
theorem _root_.solution {d : ℝ} (hd : d ≤ A * (q0 + r * (TO + D2 + 2 * r))) : d ≤ 2 * A * b := by
  have hT1 := h.one_le_order_alt
  have hT0 : (0 : ℝ) ≤ TO := by linarith
  have hA1 : (1 : ℝ) ≤ A := by linarith [h.forty_eight_le_constant]
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hr0 : (0 : ℝ) ≤ r := by linarith [h.r6]
  have hrA : r ≤ A := by linarith [h.rA]
  have hD2 := h.two_le_degree_alt
  have hQ := h.Q_le
  have hq0 := h.modulus_pos_alt
  have hq1 : q0 * 1 ≤ q0 * TO := mul_le_mul_of_nonneg_left hT1 hq0.le
  have hq : q0 ≤ b + TO := by linarith [h.q0hi]
  have e1 : r * (TO + D2 + 2 * r) ≤ A * (3 * TO) := mul_le_mul hrA hQ (by linarith) hA0
  have e2 : A * (q0 + r * (TO + D2 + 2 * r)) ≤ A * (b + TO + A * (3 * TO)) :=
    mul_le_mul_of_nonneg_left (by linarith) hA0
  have hATO : 1 ≤ A * TO := one_le_mul_of_one_le_of_one_le hA1 hT1
  have p1 : A * TO * 1 ≤ A * TO * (A * TO) := mul_le_mul_of_nonneg_left hATO (by linarith)
  have hTT : A * A * TO ≤ A * A * (TO * TO) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have eA : A * (b + TO + A * (3 * TO)) = A * b + A * TO + 3 * (A * A * TO) := by ring
  have eP : A * TO * (A * TO) = A ^ 2 * TO ^ 2 := by ring
  have eQ : A * A * (TO * TO) = A ^ 2 * TO ^ 2 := by ring
  have hB := h.toBs.ATOb
  have hP0 : (0 : ℝ) ≤ A ^ 2 * TO ^ 2 := by positivity
  have hAb := h.b_le_Ab
  linarith
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn
