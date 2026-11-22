-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.meanTransferBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:24:26.685742+00:00
-- url     : https://prove2.me/submissions/fe7b3d54-d964-4643-83a3-d3d07675b040

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementR
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean

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
theorem _root_.solution : TransferMean := by
  unfold TransferMean
  intro S _ rk nS dg nbar de la ka HH0 muP0 muPs muR0 muRs hnbar hde0 hde13 hla hka hrk hR hn
    hR0 hRs hdg hPs hP0
  rw [abs_le] at hR0 hRs
  obtain ⟨hR0a, hR0b⟩ := hR0
  obtain ⟨hRsa, hRsb⟩ := hRs
  have hD : ∑ s, dg s ≤ (∑ s, rk s) * (HH0 + ka * la) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun s _ => hdg s
  have hWlo : (1 - de) * nbar * ∑ s, rk s ≤ ∑ s, nS s * rk s := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (hn s).1 (hrk s)
  have hmuP0 : muP0 ≤ HH0 + ka * la + 2 * la := by
    have h : muP0 * ∑ s, rk s ≤ (HH0 + ka * la + 2 * la) * ∑ s, rk s := by linarith
    exact le_of_mul_le_mul_right h hR
  refine ⟨by linarith, ?_⟩
  have hW : 0 < ∑ s, nS s * rk s := by
    have : 0 < (1 - de) * nbar * ∑ s, rk s := mul_pos (mul_pos (by linarith) hnbar) hR
    linarith
  have key : ∑ s, ((HH0 + ka * la) * (nS s * rk s) - (1 + de) * nbar * ((HH0 + ka * la) * rk s)
      + (1 + de) * nbar * dg s) ≤ ∑ s, nS s * dg s := by
    refine Finset.sum_le_sum fun s _ => ?_
    nlinarith [mul_nonneg (sub_nonneg.2 (hdg s)) (sub_nonneg.2 (hn s).2)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at key
  have hnn : 0 ≤ (1 + de) * nbar := mul_nonneg (by linarith) hnbar.le
  have h3 : (1 + de) * nbar * (muP0 * ∑ s, rk s) ≤
      (1 + de) * nbar * ((∑ s, dg s) + 2 * la * ∑ s, rk s) :=
    mul_le_mul_of_nonneg_left hP0 hnn
  have hY : 0 ≤ (1 + 3 * de) * (HH0 + ka * la + 2 * la - muP0) :=
    mul_nonneg (by linarith) (by linarith)
  have h1 : (1 + 3 * de) * (HH0 + ka * la + 2 * la - muP0) * ((1 - de) * nbar * ∑ s, rk s) ≤
      (1 + 3 * de) * (HH0 + ka * la + 2 * la - muP0) * ∑ s, nS s * rk s :=
    mul_le_mul_of_nonneg_left hWlo hY
  have h2 : 0 ≤ (HH0 + ka * la + 2 * la - muP0) * nbar * (∑ s, rk s) * (de * (1 - 3 * de)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hnbar.le) hR.le)
      (mul_nonneg hde0 (by linarith))
  have hmain : (-muPs) * ∑ s, nS s * rk s ≤
      (17 / 2 * la - (HH0 + ka * la) + (1 + 3 * de) * (HH0 + ka * la + 2 * la - muP0)) *
        ∑ s, nS s * rk s := by
    linarith
  have hmuPs := le_of_mul_le_mul_right hmain hW
  have hXY : 3 * de * (HH0 + ka * la + 2 * la - muP0) ≤
      3 * de * (-muR0 + HH0 + (2 * ka + 2) * la) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith
end Formalism.BranchingDeterminantCap
