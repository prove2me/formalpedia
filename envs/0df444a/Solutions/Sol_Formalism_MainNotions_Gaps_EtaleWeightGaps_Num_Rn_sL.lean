-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn.sL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:32:40.594534+00:00
-- url     : https://prove2.me/submissions/e3647caf-3007-4848-8779-9b84dd91ed29

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_ATOb
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Rn_nW_le
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
theorem _root_.solution {s : ℝ} (hs : s ≤ A * (q0 + r * (TO + D2 + 2 * r)) + A * nW + 1) : s * TO ≤ 2 * A * b := by
  have hT1 := h.one_le_order_alt
  have hT0 : (0 : ℝ) ≤ TO := by linarith
  have hA1 : (1 : ℝ) ≤ A := by linarith [h.forty_eight_le_constant]
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hr0 : (0 : ℝ) ≤ r := by linarith [h.r6]
  have hrA : r ≤ A := by linarith [h.rA]
  have hD2 := h.two_le_degree_alt
  have hQ := h.Q_le
  have hnW := h.nW_le
  have hq := h.q0hi
  have hX : s * TO ≤ (A * (q0 + r * (TO + D2 + 2 * r)) + A * nW + 1) * TO :=
    mul_le_mul_of_nonneg_right hs hT0
  have e1 : r * (TO + D2 + 2 * r) ≤ A * (3 * TO) := mul_le_mul hrA hQ (by linarith) hA0
  have e2 : r * (TO + D2 + 2 * r) * TO ≤ A * (3 * TO) * TO := mul_le_mul_of_nonneg_right e1 hT0
  have e3 : nW * TO ≤ TO * TO := mul_le_mul_of_nonneg_right hnW hT0
  have e4 : A * (TO * q0) ≤ A * (b + TO) := mul_le_mul_of_nonneg_left hq hA0
  have e5 : A * (r * (TO + D2 + 2 * r) * TO) ≤ A * (A * (3 * TO) * TO) := mul_le_mul_of_nonneg_left e2 hA0
  have e6 : A * (nW * TO) ≤ A * (TO * TO) := mul_le_mul_of_nonneg_left e3 hA0
  have eX : (A * (q0 + r * (TO + D2 + 2 * r)) + A * nW + 1) * TO =
      A * (TO * q0) + A * (r * (TO + D2 + 2 * r) * TO) + A * (nW * TO) + TO := by ring
  have hATO : 1 ≤ A * TO := one_le_mul_of_one_le_of_one_le hA1 hT1
  have hTA : TO ≤ A * TO := le_mul_of_one_le_left hT0 hA1
  have p1 : A * TO * 1 ≤ A * TO * (A * TO) := mul_le_mul_of_nonneg_left hATO (by linarith)
  have p2 : A * TO * TO ≤ A * TO * (A * TO) := mul_le_mul_of_nonneg_left hTA (by linarith)
  have eA : A * (A * (3 * TO) * TO) = 3 * (A * TO * (A * TO)) := by ring
  have eB : A * (TO * TO) = A * TO * TO := by ring
  have eP : A * TO * (A * TO) = A ^ 2 * TO ^ 2 := by ring
  have eC : A * (b + TO) = A * b + A * TO := by ring
  have hB := h.toBs.ATOb
  have hP0 : (0 : ℝ) ≤ A ^ 2 * TO ^ 2 := by positivity
  have hAb := h.b_le_Ab
  linarith
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn
