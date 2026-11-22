-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_zcomp_comm_bmEL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:32:18.625263+00:00
-- url     : https://prove2.me/submissions/5f66e285-241f-4796-b944-2962b0eb536d

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_commute_weightedComponent_of_monomial
import Theorems.Thm_Formalism_BranchingDeterminantCap_elemDeriv_monomial_weighted
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
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (β : Fin n → ℤ) (s t : Fin n) :
    Commute (zcomp R n β) (bmEL R n s t) := by
  exact commute_weightedComponent_of_monomial (zW n) (bmEL R n s t)
    (elemDeriv_monomial_weighted R n (zW n) (fun a s t ha => by simp [zW, ha]) s t) β
end Formalism.BranchingDeterminantCap
