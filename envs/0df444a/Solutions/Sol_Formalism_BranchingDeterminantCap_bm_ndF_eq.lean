-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_ndF_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:56.768928+00:00
-- url     : https://prove2.me/submissions/aac9633f-e721-4f98-929f-e6e11678d531

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
    ndF R (n + 1) n l j = bmE R n j l + bmZ R n j l := by
  refine MvPolynomial.derivation_ext fun v => ?_
  rw [Derivation.add_apply]
  simp only [ndF, bmE, bmZ, mkDerivation_X]
  by_cases h1 : v.2 = l <;> by_cases h2 : v.1 = Fin.last n <;> simp [h1, h2]
end Formalism.BranchingDeterminantCap
