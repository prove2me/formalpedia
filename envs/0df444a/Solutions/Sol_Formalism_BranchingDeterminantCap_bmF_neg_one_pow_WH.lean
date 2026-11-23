-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmF_neg_one_pow_WH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:23:16.302005+00:00
-- url     : https://prove2.me/submissions/dffca215-4baf-4246-af21-899ac9a820e8

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
theorem _root_.solution {R σ B : Type*} [CommRing R] [AddCommMonoid B] (w : σ → B) (k : ℕ) :
    IsWeightedHomogeneous w ((-1 : MvPolynomial σ R) ^ k) 0 := by
  rw [show (-1 : MvPolynomial σ R) ^ k = C ((-1 : R) ^ k) by rw [map_pow, map_neg, map_one]]
  exact isWeightedHomogeneous_C w _
end Formalism.BranchingDeterminantCap
