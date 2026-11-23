-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.BsForm.suml
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:03.783631+00:00
-- url     : https://prove2.me/submissions/0c36c64e-a5e4-4b3b-af26-d3ab9d64ff5e

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchScale
import Theorems.Thm_Formalism_BranchingDeterminantCap_BsForm_zerol
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
theorem _root_.solution (H : BsForm sg D) {ι : Type*} (s : Finset ι) (g : ι → MvPolynomial (Fin n × Fin n) ℂ) (q) :
    D (∑ i ∈ s, g i) q = ∑ i ∈ s, D (g i) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [H.zerol]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, H.addl, ih]
end Formalism.BranchingDeterminantCap.BsForm
