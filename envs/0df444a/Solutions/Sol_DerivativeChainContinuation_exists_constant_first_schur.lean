-- Prove2me | solution 1 for DerivativeChainContinuation.exists_constant_first_schur
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:50:22.821639+00:00
-- url     : https://prove2.me/submissions/45fe94fd-6f52-4687-ac85-7c4589871102

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainContinuation_SchurExtension
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_constant_unitary_compression
import Theorems.Thm_DerivativeChainContinuation_exists_constant_first_unitary
import Theorems.Thm_DerivativeChainContinuation_exists_unitary_triangular
import Theorems.Thm_DerivativeChainContinuation_extendFirstUnitary_mem
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix
open scoped BigOperators





theorem extendFirstUnitary_tail {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (i j : Fin n) :
    ((extendFirstUnitary U).conjTranspose*M*extendFirstUnitary U) i.succ j.succ =
      (U.conjTranspose * M.submatrix Fin.succ Fin.succ * U) i j := by
  simp [extendFirstUnitary, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_succ, Matrix.submatrix_apply]

theorem extendFirstUnitary_firstColumn {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hM : ∀ i : Fin n, M i.succ 0 = 0) (i : Fin n) :
    ((extendFirstUnitary U).conjTranspose*M*extendFirstUnitary U) i.succ 0 = 0 := by
  simp [extendFirstUnitary, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_succ, hM]

end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (n : ℕ) (a : Fin (n+1) → ℂ) :
    ∃ Q : Matrix (Fin (n+1)) (Fin (n+1)) ℂ,
      Q ∈ unitaryGroup (Fin (n+1)) ℂ ∧
      (∀ i, Q i 0=((Real.sqrt (n+1:ℝ))⁻¹:ℂ)) ∧
      (Q.conjTranspose*rootCompression a*Q).IsUpperTriangular := by
  obtain ⟨Q,hQ,hfirst⟩ := exists_constant_first_unitary n
  let M := Q.conjTranspose*rootCompression a*Q
  have hcol (i : Fin n) : M i.succ 0=0 := by
    dsimp only [M]
    rw [constant_unitary_compression n a Q hQ hfirst]
    simp [Matrix.mul_apply, Matrix.diagonal_apply]
  obtain ⟨U,hU,ht⟩ := exists_unitary_triangular n (M.submatrix Fin.succ Fin.succ)
  let E := extendFirstUnitary U
  have hE : E ∈ unitaryGroup (Fin (n+1)) ℂ := extendFirstUnitary_mem U hU
  have heq : (Q*E).conjTranspose*rootCompression a*(Q*E)=E.conjTranspose*M*E := by
    simp only [conjTranspose_mul,M,Matrix.mul_assoc]
  refine ⟨Q*E,mul_mem hQ hE,?_,?_⟩
  · intro i
    simp [E,extendFirstUnitary,Matrix.mul_apply,Fin.sum_univ_succ,hfirst]
  · rw [heq]
    intro i j hji
    revert hji
    refine Fin.cases ?_ (fun i => ?_) i
    · intro h; exact (not_lt_of_ge (Fin.zero_le j) h).elim
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro _; exact extendFirstUnitary_firstColumn U M hcol i
      · intro h
        rw [extendFirstUnitary_tail]
        exact ht (Fin.succ_lt_succ_iff.mp h)
