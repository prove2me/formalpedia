-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.lastRowDeriv_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:24:42.932844+00:00
-- url     : https://prove2.me/submissions/d1b70dd7-b435-482b-9c86-63cd06e20094

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
    bmZ R n s t (X v) = if v.2 = t ∧ v.1 = Fin.last n then X (v.1, s) else 0 := by
  unfold bmZ
  exact mkDerivation_X R _ v
end Formalism.BranchingDeterminantCap
