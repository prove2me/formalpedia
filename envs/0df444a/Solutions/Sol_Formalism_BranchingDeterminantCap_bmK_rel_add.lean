-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_rel_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:56.222331+00:00
-- url     : https://prove2.me/submissions/86bed181-d0fc-43ac-8b52-af56c8129939

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_add

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
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} (lam sg : Fin n → ℕ) (f f' : ↥(dualWeyl R n n sg))
    (G G' : BP R n) (h : bmRel R n lam sg f G) (h' : bmRel R n lam sg f' G') :
    bmRel R n lam sg (f + f') (G + G') := by
  exact bmLift_add h h'
end Formalism.BranchingDeterminantCap
