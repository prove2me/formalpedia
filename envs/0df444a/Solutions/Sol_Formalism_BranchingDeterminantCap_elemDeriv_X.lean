-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.elemDeriv_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:40:44.40764+00:00
-- url     : https://prove2.me/submissions/a4c0b7da-2719-4c7e-85a0-b8f4baa70d94

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap

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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (s t : Fin n) (v : Fin (n + 1) × Fin n) :
    bmE R n s t (X v) = if v.2 = t ∧ v.1 ≠ Fin.last n then X (v.1, s) else 0 := by
  unfold bmE
  exact mkDerivation_X R _ v
end Formalism.BranchingDeterminantCap
