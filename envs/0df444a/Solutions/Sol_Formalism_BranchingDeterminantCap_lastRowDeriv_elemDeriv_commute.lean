-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.lastRowDeriv_elemDeriv_commute
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:06.937818+00:00
-- url     : https://prove2.me/submissions/7ddc5eff-18e1-4efd-b657-88e73be42420

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_elemDeriv_X
import Theorems.Thm_Formalism_BranchingDeterminantCap_lastRowDeriv_X
import Theorems.Thm_Formalism_BranchingDeterminantCap_derivation_apply_ite
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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (l j s t : Fin n) :
    ⁅bmZ R n l j, bmE R n s t⁆ = 0 := by
  refine MvPolynomial.derivation_ext fun v => ?_
  rw [Derivation.commutator_apply]
  simp only [elemDeriv_X, lastRowDeriv_X, derivation_apply_ite, map_zero, Derivation.zero_apply]
  by_cases h1 : v.1 = Fin.last n <;> simp [h1]
end Formalism.BranchingDeterminantCap
