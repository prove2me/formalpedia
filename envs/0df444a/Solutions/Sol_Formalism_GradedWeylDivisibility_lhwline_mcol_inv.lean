-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwline_mcol_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:15.631892+00:00
-- url     : https://prove2.me/submissions/ca5af693-8a74-4192-84c5-a2083c785a09

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
variable {K : Type*} [Field K] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (φ : (Fin r × Fin n → K) → K) (hφ : lhwline_CInv φ) (q : Fin n)
    (c : Fin n → K) (x : Fin r × Fin n → K) (S : Finset (Fin n)) (hS : ∀ j ∈ S, q < j) :
    φ (lhwline_mcol q S c x) = φ x := by
  revert hS
  refine Finset.induction_on S ?_ ?_
  · intro _
    congr 1
  · intro b S hbS ih hS
    have hqS : q ∉ S := fun hq => lt_irrefl q (hS q (Finset.mem_insert_of_mem hq))
    have hqb : q < b := hS b (Finset.mem_insert_self b S)
    have key : lhwline_mcol q (insert b S) c x =
        lhwline_colOp q b (c b) (lhwline_mcol q S c x) := by
      funext v
      by_cases hv : v.2 = b
      · simp [lhwline_mcol, lhwline_colOp, hv, hbS, hqS]
      · simp [lhwline_mcol, lhwline_colOp, hv, hqS]
    rw [key, hφ _ q b (c b) hqb, ih (fun d hd => hS d (Finset.mem_insert_of_mem hd))]
end Formalism.GradedWeylDivisibility
