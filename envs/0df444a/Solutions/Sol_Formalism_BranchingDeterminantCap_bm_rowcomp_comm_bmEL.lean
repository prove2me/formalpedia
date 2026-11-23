-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_rowcomp_comm_bmEL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:04.510817+00:00
-- url     : https://prove2.me/submissions/8188ad44-066d-4a5d-badb-442ca41077a9

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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (ρ : Fin (n + 1) → ℕ) (s t : Fin n) :
    Commute (weightedHomogeneousComponent (rowW (n + 1) n) ρ : Module.End R (BP R n)) (bmEL R n s t) := by
  exact commute_weightedComponent_of_monomial (rowW (n + 1) n) (bmEL R n s t)
    (elemDeriv_monomial_weighted R n (rowW (n + 1) n) (fun a s t _ => rfl) s t) ρ
end Formalism.BranchingDeterminantCap
