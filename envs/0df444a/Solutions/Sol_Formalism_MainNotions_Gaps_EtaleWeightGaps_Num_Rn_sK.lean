-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn.sK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:39:41.829752+00:00
-- url     : https://prove2.me/submissions/1687f69e-9400-4ab6-bac6-2a9a83ca0c78

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Bs_ATOb
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Rn_nW_le
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Rn_kl_le
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_Num_Rn_TQ_le
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
theorem _root_.solution {s : ℝ} (hs : s ≤ A * (D2 * nW + 2 * r + (TO + D2) * q0 + r * ((TO + D2) * (TO + D2 + 2 * r))) +
    A * (nP + TO * nW) + 1) : s ≤ 4 * A * b := by
  have hT1 := h.one_le_order_alt
  have hT0 : (0 : ℝ) ≤ TO := by linarith
  have hA1 : (1 : ℝ) ≤ A := by linarith [h.forty_eight_le_constant]
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hr0 : (0 : ℝ) ≤ r := by linarith [h.r6]
  have hrA : r ≤ A := by linarith [h.rA]
  have hD2 := h.two_le_degree_alt
  have hkl := h.kl_le
  have hTQ := h.TQ_le
  have hY0 : 0 ≤ (TO + D2) * (TO + D2 + 2 * r) := mul_nonneg (by linarith) (by linarith)
  have e1 : r * ((TO + D2) * (TO + D2 + 2 * r)) ≤ A * (6 * TO ^ 2) :=
    mul_le_mul hrA hTQ hY0 hA0
  have hnW := h.nW_le
  have hnP : nP ≤ TO := le_trans h.nPW hnW
  have e2 : TO * nW ≤ TO * TO := mul_le_mul_of_nonneg_left hnW hT0
  have hATO : 1 ≤ A * TO := one_le_mul_of_one_le_of_one_le hA1 hT1
  have hTA : TO ≤ A * TO := le_mul_of_one_le_left hT0 hA1
  have p1 : A * TO * 1 ≤ A * TO * (A * TO) := mul_le_mul_of_nonneg_left hATO (by linarith)
  have p2 : A * TO * TO ≤ A * TO * (A * TO) := mul_le_mul_of_nonneg_left hTA (by linarith)
  have eP : A * TO * (A * TO) = A ^ 2 * TO ^ 2 := by ring
  have hB := h.toBs.ATOb
  have hBA := h.b_le_Ab
  have i1 : A * (D2 * nW + 2 * r + (TO + D2) * q0 + r * ((TO + D2) * (TO + D2 + 2 * r))) ≤
      A * (3 * TO + 2 * b + A * (6 * TO ^ 2)) := mul_le_mul_of_nonneg_left (by linarith) hA0
  have i2 : A * (nP + TO * nW) ≤ A * (TO + TO * TO) := mul_le_mul_of_nonneg_left (by linarith) hA0
  have f1 : A * (3 * TO + 2 * b + A * (6 * TO ^ 2)) = 2 * (A * b) + 3 * (A * TO) + 6 * (A ^ 2 * TO ^ 2) := by ring
  have f2 : A * (TO + TO * TO) = A * TO + A * TO * TO := by ring
  have hP0 : (0 : ℝ) ≤ A ^ 2 * TO ^ 2 := by positivity
  have f3 : A * b = A * b := rfl
  have hAb : b ≤ A * b := hBA
  nlinarith
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Rn
