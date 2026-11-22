-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmD_zcomp_bmE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:58.656112+00:00
-- url     : https://prove2.me/submissions/46cf328c-da58-477a-bf53-39c648bf30f6

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_zcomp_comm_bmEL
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmE_comm_apply

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
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} (β : Fin n → ℤ) (s t : Fin n) (Y : BP R n) :
    zcomp R n β (bmE R n s t Y) = bmE R n s t (zcomp R n β Y) := by
  exact bmE_comm_apply (bm_zcomp_comm_bmEL R n β s t) Y
end Formalism.BranchingDeterminantCap
