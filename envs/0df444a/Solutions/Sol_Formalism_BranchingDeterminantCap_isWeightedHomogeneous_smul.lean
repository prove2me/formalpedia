-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.isWeightedHomogeneous_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:45:15.368817+00:00
-- url     : https://prove2.me/submissions/ace98560-c607-4dfd-ae5d-b56b379aacae

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
theorem _root_.solution {R σ B : Type*} [CommRing R] [AddCommMonoid B] {w : σ → B} {β : B}
    {F : MvPolynomial σ R} (hF : IsWeightedHomogeneous w F β) (c : R) :
    IsWeightedHomogeneous w (c • F) β := by
  intro d hd
  apply hF
  intro h0
  apply hd
  rw [coeff_smul, h0, smul_zero]
end Formalism.BranchingDeterminantCap
