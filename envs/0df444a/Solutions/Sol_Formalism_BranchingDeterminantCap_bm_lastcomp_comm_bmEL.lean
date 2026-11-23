-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_lastcomp_comm_bmEL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:56.783703+00:00
-- url     : https://prove2.me/submissions/40f1ad64-b138-4c9f-b2ab-be7389badbf1

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_commute_weightedComponent_of_monomial
import Theorems.Thm_Formalism_BranchingDeterminantCap_elemDeriv_monomial_weighted

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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (d : ℕ) (s t : Fin n) :
    Commute (weightedHomogeneousComponent (lastW n) d : Module.End R (BP R n)) (bmEL R n s t) := by
  exact commute_weightedComponent_of_monomial (lastW n) (bmEL R n s t) (elemDeriv_monomial_weighted R n (lastW n) (fun a s t _ => rfl) s t) d
end Formalism.BranchingDeterminantCap
