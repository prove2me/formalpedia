-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmK_mem_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:36:56.109777+00:00
-- url     : https://prove2.me/submissions/41a02719-c90c-4cd2-a82c-17ae7e63e48b

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
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} {lam : Fin n → ℕ} {d : ℕ} {G : BP R n} :
    G ∈ bmW R n lam d ↔ G ∈ dualWeyl R (n + 1) n lam ∧ IsWeightedHomogeneous (lastW n) G d := by
  exact Iff.rfl
end Formalism.BranchingDeterminantCap
