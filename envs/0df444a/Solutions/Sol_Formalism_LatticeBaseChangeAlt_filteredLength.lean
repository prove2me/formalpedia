-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.filteredLength
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:32:47.678985+00:00
-- url     : https://prove2.me/submissions/cbc7b59c-751b-4feb-93e4-5b37173a68b9

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_LogFactorialIndices_LogProductFormula
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_ReductionQuotient
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BasisReduction_q_congr
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BasisReduction_q_chain
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BasisReduction_q_sup
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BasisReduction_q_zero
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BasisReduction_q_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
open BasisReduction
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : FilteredLength := by
  intro O A _ _ _ n F h0 hn hF N
  have key : ∀ k, Module.length O (A ⧸ N) =
      ∑ j ∈ Finset.range k, q (F j) (F (j + 1) ⊔ (N ⊓ F j)) + q (F k) N := by
    intro k
    induction k with
    | zero => simp [h0, q_top]
    | succ k ih =>
      rw [ih, Finset.sum_range_succ, add_assoc]
      congr 1
      have hB : F (k + 1) ⊔ (N ⊓ F k) ≤ F k := sup_le (hF k) inf_le_right
      calc q (F k) N = q (F k) (N ⊓ F k) := q_congr _ (by rw [inf_comm N, ← inf_assoc, inf_idem])
        _ = q (F k) (F (k + 1) ⊔ (N ⊓ F k)) + q (F (k + 1) ⊔ (N ⊓ F k)) (N ⊓ F k) :=
            q_chain le_sup_right hB
        _ = q (F k) (F (k + 1) ⊔ (N ⊓ F k)) + q (F (k + 1)) (N ⊓ F k) := by rw [q_sup]
        _ = q (F k) (F (k + 1) ⊔ (N ⊓ F k)) + q (F (k + 1)) N := by
            rw [q_congr (F (k + 1)) (B := N ⊓ F k) (B' := N)]
            rw [inf_comm N, ← inf_assoc, inf_eq_left.mpr (hF k)]
  rw [key n, hn, q_zero bot_le, add_zero]
end Formalism.LatticeBaseChangeAlt
