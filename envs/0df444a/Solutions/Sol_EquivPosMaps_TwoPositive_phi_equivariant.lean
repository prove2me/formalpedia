-- Prove2me | solution 1 for EquivPosMaps.TwoPositive.phi_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T21:14:34.506007+00:00
-- url     : https://prove2.me/submissions/697151de-62db-43fc-b137-cc421cde90c1

import Mathlib
import Definitions.Def_EquivPosMaps_TwoPositive_Basic

open scoped Matrix Kronecker ComplexOrder
open EquivPosMaps.TwoPositive Matrix

theorem solution (n : ℕ) (hn : 3 ≤ n) (α β : ℝ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    phi n α β ((U : Matrix (Fin n) (Fin n) ℂ) * X * star (U : Matrix (Fin n) (Fin n) ℂ)) =
      (((U : Matrix (Fin n) (Fin n) ℂ).map star) ⊗ₖ
        (U : Matrix (Fin n) (Fin n) ℂ)) * phi n α β X *
          ((((U : Matrix (Fin n) (Fin n) ℂ).map star) ⊗ₖ
            (U : Matrix (Fin n) (Fin n) ℂ))ᴴ) := by
  obtain ⟨V, hVm⟩ := U
  simp only []
  have h1 : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hVm
  have h2 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hVm
  have hstar : star V = Vᴴ := rfl
  have hbarH : (V.map star)ᴴ = Vᵀ := by
    ext i j; simp [Matrix.conjTranspose_apply]
  have hbar1 : V.map star * Vᵀ = 1 := by
    have := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_one] at this
    rwa [show (Vᴴ)ᵀ = V.map star by ext i j; simp [Matrix.conjTranspose_apply]] at this
  have htr : (V * X * Vᴴ).trace = X.trace := by
    rw [Matrix.trace_mul_comm, ← mul_assoc, h2, one_mul]
  have hT : (V * X * Vᴴ)ᵀ = V.map star * Xᵀ * Vᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul,
      show (Vᴴ)ᵀ = V.map star by ext i j; simp [Matrix.conjTranspose_apply], mul_assoc]
  have hW : (V.map star ⊗ₖ V)ᴴ = Vᵀ ⊗ₖ Vᴴ := by
    rw [Matrix.conjTranspose_kronecker, hbarH]
  have hW1 : (V.map star ⊗ₖ V) * (Vᵀ ⊗ₖ Vᴴ) = 1 := by
    rw [← Matrix.mul_kronecker_mul, hbar1, h1, Matrix.one_kronecker_one]
  have hBell : (V.map star ⊗ₖ V) * bellProj n * (Vᵀ ⊗ₖ Vᴴ) = bellProj n := by
    ext ⟨p1, p2⟩ ⟨q1, q2⟩
    have e1 : ∀ a b : Fin n, (V * Vᴴ) a b = if a = b then 1 else 0 := by
      intro a b; rw [h1, Matrix.one_apply]
    simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, bellProj, Matrix.of_apply,
      Fintype.sum_prod_type, Matrix.transpose_apply, Matrix.map_apply] at e1 ⊢
    simp only [mul_ite, mul_one, mul_zero, ite_and, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.mul_sum, e1 q1 q2]
    have e2 : ∑ x, star (V p1 x) * V p2 x = if p1 = p2 then 1 else 0 := by
      have := e1 p2 p1
      simp only [Matrix.conjTranspose_apply] at this
      rw [show (if p1 = p2 then (1:ℂ) else 0) = if p2 = p1 then 1 else 0 by
        by_cases h : p1 = p2 <;> simp [h, eq_comm]]
      rw [← this]; exact Finset.sum_congr rfl fun x _ => mul_comm _ _
    rw [e2]
    split_ifs <;> simp
  have hK : ∀ A B : Matrix (Fin n) (Fin n) ℂ,
      (V.map star ⊗ₖ V) * (A ⊗ₖ B) * (Vᵀ ⊗ₖ Vᴴ) = (V.map star * A * Vᵀ) ⊗ₖ (V * B * Vᴴ) := by
    intro A B; rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  show (V * X * star V)ᵀ ⊗ₖ 1 + 1 ⊗ₖ (V * X * star V) + (V * X * star V).trace •
      ((α : ℂ) • (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) + (β : ℂ) • bellProj n) =
    (V.map star ⊗ₖ V) * (Xᵀ ⊗ₖ 1 + 1 ⊗ₖ X + X.trace • ((α : ℂ) • 1 + (β : ℂ) • bellProj n)) *
      (V.map star ⊗ₖ V)ᴴ
  rw [hW, hstar, htr, hT]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hK, hBell,
    Matrix.mul_one, hW1, hbar1, h1]

