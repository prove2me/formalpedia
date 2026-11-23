-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmF_zmon_WH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:08.093521+00:00
-- url     : https://prove2.me/submissions/9d337223-29e7-4fde-a6cc-66475f63f76e

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_pow
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (b : Fin n → ℕ) :
    IsWeightedHomogeneous (zW n) (zmon R n b) (fun s => (b s : ℤ)) := by
  have hX : ∀ s, IsWeightedHomogeneous (zW n) (X (Fin.last n, s) : BP R n) (zW n (Fin.last n, s)) :=
    fun s => by apply isWeightedHomogeneous_X
  have e : (fun s => (b s : ℤ)) = ∑ s, b s • zW n (Fin.last n, s) := by
    funext t
    simp [zW, Finset.sum_apply, Pi.single_apply]
  rw [e]
  exact IsWeightedHomogeneous.prod Finset.univ _ _ (fun s _ => (hX s).pow (b s))
end Formalism.BranchingDeterminantCap
