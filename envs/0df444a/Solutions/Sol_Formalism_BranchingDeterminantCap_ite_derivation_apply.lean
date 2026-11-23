-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.ite_derivation_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:06.767821+00:00
-- url     : https://prove2.me/submissions/1a6bd633-c504-4871-bd9a-99e73fcc5b0a

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
    (D : Derivation R A A) (x : A) : (if c then D else 0) x = if c then D x else 0 := by
  split_ifs <;> simp
end Formalism.BranchingDeterminantCap
