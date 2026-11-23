-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmG_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:23.50651+00:00
-- url     : https://prove2.me/submissions/f5730b4e-8e12-4b82-ab82-a854a0d57342

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_mul
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmLift_one
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
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} {ι : Type*} (s : Finset ι) (lam b : ι → Fin n → ℕ)
    (f : ι → MvPolynomial (Fin n × Fin n) R) (G : ι → BP R n)
    (h : ∀ i ∈ s, bmLift R n (lam i) (b i) (f i) (G i)) :
    bmLift R n (∑ i ∈ s, lam i) (∑ i ∈ s, b i) (∏ i ∈ s, f i) (∏ i ∈ s, G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bmLift_one R n
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]
    exact bmLift_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end Formalism.BranchingDeterminantCap
