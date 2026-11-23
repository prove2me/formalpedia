-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmA_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:31.35694+00:00
-- url     : https://prove2.me/submissions/b646314d-8ba5-4e5b-96d9-f1c2422e8019

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
variable {A : Type*} [Ring A]
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (c X Y : A) (hX : c * X = X * c) (hY : c * Y = Y * c) (P Q : Prop) [Decidable P] [Decidable Q] :
    ((if P then c else 0) - X) * ((if Q then c + 1 else 0) - Y) -
        ((if Q then c else 0) - Y) * ((if P then c + 1 else 0) - X) =
      (if P then Y else 0) - (if Q then X else 0) + (X * Y - Y * X) := by
  split_ifs <;>
    (try simp only [mul_sub, sub_mul, mul_add, add_mul, mul_one, one_mul, mul_zero, zero_mul, sub_zero,
      zero_sub, neg_mul, mul_neg]) <;>
    (try simp only [← hX, ← hY]) <;> abel
end Formalism.BranchingDeterminantCap
