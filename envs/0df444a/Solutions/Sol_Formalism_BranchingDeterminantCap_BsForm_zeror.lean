-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.BsForm.zeror
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:56.099621+00:00
-- url     : https://prove2.me/submissions/f999f9ca-25c9-48d4-8d0f-64b43d8ed634

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
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
open Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.BranchingDeterminantCap.BsForm
variable {n : ℕ} {sg : Fin n → ℕ}
  {D : MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ → ℂ}
namespace Formalism.BranchingDeterminantCap.BsForm
theorem _root_.solution (H : BsForm sg D) (p) : D p 0 = 0 := by
  have := H.smulr 0 p 0
  simpa using this
end Formalism.BranchingDeterminantCap.BsForm
