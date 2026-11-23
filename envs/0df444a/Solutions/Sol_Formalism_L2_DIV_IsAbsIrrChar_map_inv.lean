-- Prove2me | solution 1 for Formalism.L2.DIV.IsAbsIrrChar.map_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:59:08.596431+00:00
-- url     : https://prove2.me/submissions/dde5309f-0c3b-44b8-bd07-77209c7fedf1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_trace_inv_of_pow_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace Formalism.L2.DIV
namespace IsAbsIrrChar
theorem _root_.solution {χ : G → K} (h : IsAbsIrrChar χ) (σ : K →+* ℂ) (t : G) :
    σ (χ t⁻¹) = starRingEnd ℂ (σ (χ t)) := by
  obtain ⟨n, ρ, -, hρ⟩ := h
  let _ : Algebra K ℂ := σ.toAlgebra
  let τ : AlgebraicClosure K →ₐ[K] ℂ := IsAlgClosed.lift
  have hτ : ∀ x : K, τ (algebraMap K (AlgebraicClosure K) x) = σ x := fun x => τ.commutes x
  let A : G → Matrix (Fin n) (Fin n) (AlgebraicClosure K) := fun s => LinearMap.toMatrix' (ρ s)
  have hA : ∀ s, (A s).trace = algebraMap K (AlgebraicClosure K) (χ s) := by
    intro s
    rw [← hρ s, Representation.character, LinearMap.trace_eq_matrix_trace _ (Pi.basisFun _ (Fin n))]
    rfl
  have hmul : ∀ s u, A (s * u) = A s * A u := by
    intro s u
    simp only [A, map_mul, Module.End.mul_eq_comp, LinearMap.toMatrix'_comp]
  have hone : A 1 = 1 := by simp [A, Module.End.one_eq_id]
  have htr : ∀ s, ((A s).map τ).trace = σ (χ s) := by
    intro s
    rw [← hτ, ← hA s, Matrix.trace, Matrix.trace, map_sum]
    rfl
  have hmap : ∀ s u, (A (s * u)).map τ = (A s).map τ * (A u).map τ := by
    intro s u
    rw [hmul, Matrix.map_mul]
  have hpow : ∀ k : ℕ, ((A t).map τ) ^ k = (A (t ^ k)).map τ := by
    intro k
    induction k with
    | zero => simp [hone]
    | succ k ih => rw [pow_succ, pow_succ, ih, hmap]
  rw [← htr, ← htr]
  refine trace_inv_of_pow_eq_one _ _ (N := Fintype.card G) Fintype.card_ne_zero ?_ ?_
  · rw [hpow, pow_card_eq_one, hone]; simp
  · rw [← hmap, inv_mul_cancel, hone]; simp
end IsAbsIrrChar
end Formalism.L2.DIV
