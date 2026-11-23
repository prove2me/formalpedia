-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_Zc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:16.946547+00:00
-- url     : https://prove2.me/submissions/3d7c0cc3-6bba-4b9f-81f6-7ba83f8e0f15

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_capDet_commute_of
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_list_comm

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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (lam sg : Fin n → ℕ) (x : Module.End R (BP R n))
    (hx : ∀ i j, Commute x (bmEL R n i j)) : Commute x (bmZop R n lam sg) := by
  exact bmK_list_comm (bmCap R n) x (fun u => capDet_commute_of (bmEL R n) u x hx) (bmList lam sg)
end Formalism.BranchingDeterminantCap
