-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwline_mrow_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:11.93502+00:00
-- url     : https://prove2.me/submissions/d292e71e-4db9-4800-81bf-ccd8d81c1941

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
theorem _root_.solution (φ : (Fin r × Fin n → K) → K) (hφ : lhwline_RInv φ) (p : Fin r)
    (t : Fin r → K) (x : Fin r × Fin n → K) (S : Finset (Fin r)) (hS : ∀ b ∈ S, p < b) :
    φ (lhwline_mrow p S t x) = φ x := by
  revert hS
  refine Finset.induction_on S ?_ ?_
  · intro _
    congr 1
  · intro b S hbS ih hS
    have hpS : p ∉ S := fun hp => lt_irrefl p (hS p (Finset.mem_insert_of_mem hp))
    have hpb : p < b := hS b (Finset.mem_insert_self b S)
    have key : lhwline_mrow p (insert b S) t x =
        lhwline_rowOp p b (t b) (lhwline_mrow p S t x) := by
      funext v
      by_cases hv : v.1 = b
      · simp [lhwline_mrow, lhwline_rowOp, hv, hbS, hpS]
      · simp [lhwline_mrow, lhwline_rowOp, hv, hpS]
    rw [key, hφ _ p b (t b) hpb, ih (fun c hc => hS c (Finset.mem_insert_of_mem hc))]
end Formalism.GradedWeylDivisibility
