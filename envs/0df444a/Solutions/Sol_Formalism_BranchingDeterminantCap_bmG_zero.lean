-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmG_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:27:45.580456+00:00
-- url     : https://prove2.me/submissions/5a00ce8c-c614-4016-8b26-6ff81b6356a2

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmF_low_zero

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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (lam b : Fin n → ℕ) : bmLift R n lam b 0 0 := by
  refine ⟨Submodule.zero_mem _, ?_, ?_⟩
  · apply isWeightedHomogeneous_zero
  · rw [map_zero, mul_zero, sub_zero]
    exact bmF_low_zero _
end Formalism.BranchingDeterminantCap
