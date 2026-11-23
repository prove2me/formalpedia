-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.meanShiftAssembly
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:07.40046+00:00
-- url     : https://prove2.me/submissions/ce55ff86-1a26-4ca4-a957-6d0ab0201f06

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementR
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Theorems.Thm_Formalism_BranchingDeterminantCap_meanTransferBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : PassageAssembly := by
  unfold PassageAssembly
  intro S _ rk nS dg nbar lam0 HH0 muP0 muPs mu0 muC f r g Q C0 hnbar hlam0 hrk hR hf hr hg hn
    h0 hC hdg hPs hP0 hZQ hQ hfrQ hC0
  have hde0 : 0 ≤ 8 * f * r / g :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hf) hr) hg.le
  have hdeQ : 8 * f * r / g * (3 * Q) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hg]
    linarith
  have hMT := meanTransferBound
  unfold TransferMean at hMT
  set de := 8 * f * r / g with hde
  have hde13 : de ≤ 1 / 3 := by nlinarith [mul_nonneg hde0 (sub_nonneg.2 hQ)]
  obtain ⟨_, hB⟩ := hMT S rk nS dg nbar de lam0 1 HH0 muP0 muPs (-mu0) (-muC) hnbar hde0 hde13
    hlam0 zero_le_one hrk hR hn (by rw [one_mul]; exact h0) (by rw [one_mul]; exact hC)
    (fun s => by rw [one_mul]; exact hdg s) hPs hP0
  have hZ : 3 * de * (mu0 + HH0 + 4 * lam0) ≤ 3 * de * Q :=
    mul_le_mul_of_nonneg_left hZQ (by linarith)
  have hC' : 0 ≤ (C0 - 25 / 2) * lam0 := mul_nonneg (by linarith) hlam0
  constructor <;> linarith
end Formalism.BranchingDeterminantCap
