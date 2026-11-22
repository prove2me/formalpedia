-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmE_comm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:31:39.8539+00:00
-- url     : https://prove2.me/submissions/fac73907-432b-4dd8-af81-1d6a18ccfa16

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
theorem _root_.solution {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {a b : Module.End R M}
    (h : Commute a b) (x : M) : a (b x) = b (a x) := by
  exact LinearMap.congr_fun h.eq x
end Formalism.BranchingDeterminantCap
