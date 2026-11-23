-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmE_eq_zero_of_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:32.111174+00:00
-- url     : https://prove2.me/submissions/8634e6a6-354b-4948-898f-bcd83cb07586

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
theorem _root_.solution {R σ B : Type*} [CommRing R] [AddCommMonoid B] (w : σ → B)
    (G : MvPolynomial σ R) (h : ∀ β, weightedHomogeneousComponent w β G = 0) : G = 0 := by
  classical
  ext d
  have := congrArg (coeff d) (h (Finsupp.weight w d))
  rw [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at this
  rw [this, coeff_zero]
end Formalism.BranchingDeterminantCap
