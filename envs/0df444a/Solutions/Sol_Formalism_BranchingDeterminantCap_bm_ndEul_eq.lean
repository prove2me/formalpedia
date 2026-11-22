-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_ndEul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:30:12.355784+00:00
-- url     : https://prove2.me/submissions/a819c2a2-e180-4de5-be96-7591391312c4

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_ndE_eq
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_ndE_self

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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (s : Fin n) :
    ndEul R (n + 1) n s = bmE R n s s + bmZ R n s s := by
  rw [← bm_ndE_self R (n + 1) n s, bm_ndE_eq]
end Formalism.BranchingDeterminantCap
