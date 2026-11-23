-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.degreeTransferBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:06.327793+00:00
-- url     : https://prove2.me/submissions/d572e32d-214f-40d2-a220-6ada129ce344

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
theorem _root_.solution : TransferDeg := by
  unfold TransferDeg
  intro S _ rk nS dgA dgB la degP h1 h2 h3 hla hR
  have hR0 : 0 ≤ ∑ s, nS s * rk s := Finset.sum_nonneg fun s _ => hR s
  have hBA : |∑ s, dgB s - ∑ s, nS s * dgA s| ≤ 13 / 2 * la * ∑ s, nS s * rk s := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => h1 s)
  have hlR : 0 ≤ la * ∑ s, nS s * rk s := mul_nonneg hla hR0
  rw [abs_le] at hBA ⊢
  obtain ⟨hBA1, hBA2⟩ := hBA
  constructor <;> linarith
end Formalism.BranchingDeterminantCap
