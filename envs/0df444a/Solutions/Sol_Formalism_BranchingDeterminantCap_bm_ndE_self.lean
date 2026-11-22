-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_ndE_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:24:03.79146+00:00
-- url     : https://prove2.me/submissions/e113b535-052b-4d5c-ac6c-1a707b5e97ff

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
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
theorem _root_.solution (R : Type*) [CommRing R] (r n : ℕ) (s : Fin n) : ndE R r n s s = ndEul R r n s := by
  refine MvPolynomial.derivation_ext fun v => ?_
  simp only [ndE, ndEul, mkDerivation_X, colW]
  by_cases h : v.2 = s
  · subst h
    simp
  · simp [h, Pi.single_apply, Ne.symm h]
end Formalism.BranchingDeterminantCap
