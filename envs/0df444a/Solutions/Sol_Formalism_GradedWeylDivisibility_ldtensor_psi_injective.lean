-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldtensor_psi_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:09.939888+00:00
-- url     : https://prove2.me/submissions/dbba1927-cf4b-4a1d-92b1-5971c866edda

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.Localization.Module
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_TensorBasis
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldtensor_glue_injective
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldtensor_prod_monomial
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldtensor_psi_tprod
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
variable (K : Type*) [Field K] {S : Type*} [Fintype S] [DecidableEq S] {k n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : Function.Injective (ldtensor_psi K (S := S) (k := k) (n := n)) := by
  classical
  let B := Basis.piTensorProduct (fun _ : S => MvPolynomial.basisMonomials (Fin k × Fin n) K)
  have hB : ∀ α, B α = tprod K (fun s => monomial (α s) (1 : K)) := fun α => by
    simp [B, Basis.piTensorProduct_apply, MvPolynomial.coe_basisMonomials]
  have hli : LinearIndependent K (ldtensor_psi K ∘ B) := by
    have e : ldtensor_psi K ∘ B = fun α => monomial (∑ t, (α t).mapDomain (Prod.mk t)) (1 : K) := by
      funext α
      simp only [Function.comp_apply, hB, ldtensor_psi_tprod, ldtensor_prod_monomial]
    rw [e]
    have h := (MvPolynomial.basisMonomials (S × (Fin k × Fin n)) K).linearIndependent.comp _
      (ldtensor_glue_injective (S := S) (k := k) (n := n))
    have e2 : (fun α : S → (Fin k × Fin n →₀ ℕ) => monomial (∑ t, (α t).mapDomain (Prod.mk t)) (1 : K)) =
        ⇑(MvPolynomial.basisMonomials (S × (Fin k × Fin n)) K) ∘
          (fun α => ∑ t, (α t).mapDomain (Prod.mk t)) := by
      funext α
      simp [MvPolynomial.coe_basisMonomials]
    rw [e2]
    exact h
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  rw [← B.linearCombination_repr x] at hx ⊢
  rw [Finsupp.apply_linearCombination] at hx
  have h0 := (linearIndependent_iff.mp hli) _ hx
  rw [h0, map_zero]
end Formalism.GradedWeylDivisibility
