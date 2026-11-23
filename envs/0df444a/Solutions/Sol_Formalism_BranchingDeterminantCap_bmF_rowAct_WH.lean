-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmF_rowAct_WH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:14.303894+00:00
-- url     : https://prove2.me/submissions/4fbf16ca-f89c-424d-8946-af7839613e89

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_rowAct_monomial_WH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (R : Type*) [CommRing R] {n : ℕ} {B : Type*} [AddCommMonoid B]
    (w : Fin (n + 1) × Fin n → B) (hw : ∀ a b s : Fin n, w (a.castSucc, s) = w (b.castSucc, s))
    (g : Matrix (Fin n) (Fin n) R) (F : BP R n) (β : B) (hF : IsWeightedHomogeneous w F β) :
    IsWeightedHomogeneous w (rowAct R (extM R g) F) β := by
  rw [F.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have := bmF_rowAct_monomial_WH R w hw g d (coeff d F)
  rwa [hF (mem_support_iff.mp hd)] at this
end Formalism.BranchingDeterminantCap
