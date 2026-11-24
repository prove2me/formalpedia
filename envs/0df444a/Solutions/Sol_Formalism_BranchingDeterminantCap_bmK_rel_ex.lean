-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_rel_ex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:33.7158+00:00
-- url     : https://prove2.me/submissions/860327be-1446-4ab8-944c-4de93dbf5f34

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_exists

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
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] {n : ℕ} (lam sg : Fin n → ℕ)
    (hIL : bmIL lam sg) (f : ↥(dualWeyl R n n sg)) : ∃ G, bmRel R n lam sg f G := by
  exact bmLift_exists lam sg hIL (f : MvPolynomial (Fin n × Fin n) R) f.2
end Formalism.BranchingDeterminantCap
