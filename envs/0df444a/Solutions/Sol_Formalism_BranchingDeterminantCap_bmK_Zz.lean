-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_Zz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:15.022104+00:00
-- url     : https://prove2.me/submissions/e9d18bf0-3ff9-4416-a42a-f0a1ba14dc1b

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_zcomp_comm_bmEL
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmE_comm_apply
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmK_Zc

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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (lam sg : Fin n → ℕ) (β : Fin n → ℤ) (G : BP R n) :
    zcomp R n β (bmZop R n lam sg G) = bmZop R n lam sg (zcomp R n β G) := by
  exact bmE_comm_apply (bmK_Zc R n lam sg (zcomp R n β) (fun i j => bm_zcomp_comm_bmEL R n β i j)) G
end Formalism.BranchingDeterminantCap
