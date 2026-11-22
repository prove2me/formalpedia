-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.derivation_apply_ite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:27:11.603425+00:00
-- url     : https://prove2.me/submissions/e7df5bd7-abc6-49fa-91e4-756954d6fafa

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (c : Prop) [Decidable c]
    (D : Derivation R A A) (x : A) : D (if c then x else 0) = if c then D x else 0 := by
  split_ifs <;> simp
end Formalism.BranchingDeterminantCap
