-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldtensor_prod_mem_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:51.724735+00:00
-- url     : https://prove2.me/submissions/c859a702-53d8-47a1-beb0-7e9ab6aae2db

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.Localization.Module
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_TensorBasis
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
open MvPolynomial PiTensorProduct
open scoped Pointwise
open Module
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] {S : Type*}
    (T : Finset S) (N : S → Submodule R A) (x : S → A) (hx : ∀ s ∈ T, x s ∈ N s) :
    ∏ s ∈ T, x s ∈ ∏ s ∈ T, N s := by
  classical
  revert hx
  refine Finset.induction_on T ?_ ?_
  · intro _
    simp only [Finset.prod_empty]
    exact Submodule.one_le.mp le_rfl
  · intro s T hs ih hx
    rw [Finset.prod_insert hs, Finset.prod_insert hs]
    exact Submodule.mul_mem_mul (hx s (Finset.mem_insert_self s T))
      (ih fun t ht => hx t (Finset.mem_insert_of_mem ht))
end Formalism.GradedWeylDivisibility
