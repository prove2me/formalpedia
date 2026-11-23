-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.elemDeriv_lie_bracket
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:40.182397+00:00
-- url     : https://prove2.me/submissions/47d14b0d-55b5-4afd-b016-312d3fee5812

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_elemDeriv_X
import Theorems.Thm_Formalism_BranchingDeterminantCap_ite_derivation_apply
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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (i j k l : Fin n) :
    ⁅bmE R n i j, bmE R n k l⁆ =
      (if j = k then bmE R n i l else 0) - (if i = l then bmE R n k j else 0) := by
  refine MvPolynomial.derivation_ext fun v => ?_
  rw [Derivation.commutator_apply, Derivation.sub_apply, ite_derivation_apply, ite_derivation_apply]
  simp only [elemDeriv_X, derivation_apply_ite, map_zero]
  by_cases h1 : v.2 = l <;> by_cases h2 : v.2 = j <;> by_cases h3 : j = k <;> by_cases h4 : i = l <;>
    by_cases h5 : v.1 = Fin.last n <;> simp_all
  all_goals (try (intros; simp_all))
end Formalism.BranchingDeterminantCap
