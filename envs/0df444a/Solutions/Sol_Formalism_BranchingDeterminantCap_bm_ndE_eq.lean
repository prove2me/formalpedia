-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_ndE_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:29.732647+00:00
-- url     : https://prove2.me/submissions/4f467647-dc36-445a-985d-77a425fc5eda

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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (l j : Fin n) :
    ndE R (n + 1) n l j = bmE R n l j + bmZ R n l j := by
  refine MvPolynomial.derivation_ext fun v => ?_
  rw [Derivation.add_apply]
  simp only [ndE, bmE, bmZ, mkDerivation_X]
  by_cases h1 : v.2 = j <;> by_cases h2 : v.1 = Fin.last n <;> simp [h1, h2]
end Formalism.BranchingDeterminantCap
