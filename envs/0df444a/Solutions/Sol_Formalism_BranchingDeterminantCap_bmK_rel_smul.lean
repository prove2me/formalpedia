-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_rel_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:01.807347+00:00
-- url     : https://prove2.me/submissions/bd90070d-ced9-4d3d-ae38-8045f420f6c1

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_smul

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
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} (lam sg : Fin n → ℕ) (c : R) (f : ↥(dualWeyl R n n sg))
    (G : BP R n) (h : bmRel R n lam sg f G) : bmRel R n lam sg (c • f) (c • G) := by
  exact bmLift_smul c h
end Formalism.BranchingDeterminantCap
