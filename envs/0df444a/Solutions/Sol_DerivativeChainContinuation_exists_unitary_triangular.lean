-- Prove2me | solution 1 for DerivativeChainContinuation.exists_unitary_triangular
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T18:24:14.910207+00:00
-- url     : https://prove2.me/submissions/4c5336df-b520-427f-8eda-66df0d0b4f25

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SchurExtension
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_exists_unitary_first_column
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
theorem solution (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ,
      U ∈ unitaryGroup (Fin n) ℂ ∧ (U.conjTranspose*A*U).IsUpperTriangular := by
  induction n with
  | zero =>
    refine ⟨1, one_mem _, ?_⟩
    intro i
    exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨Q, hQ, hcol⟩ := exists_unitary_first_column n A
    let M := Q.conjTranspose*A*Q
    obtain ⟨U, hU, ht⟩ := ih (M.submatrix Fin.succ Fin.succ)
    let E := extendFirstUnitary U
    have hE := extendFirstUnitary_mem U hU
    refine ⟨Q*E, mul_mem hQ hE, ?_⟩
    have heq : (Q*E).conjTranspose*A*(Q*E) = E.conjTranspose*M*E := by
      simp only [conjTranspose_mul, M, Matrix.mul_assoc]
    rw [heq]
    intro i j hji
    revert hji
    refine Fin.cases ?_ (fun i => ?_) i
    · intro h
      exact (not_lt_of_ge (Fin.zero_le j) h).elim
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro _
        exact extendFirstUnitary_firstColumn U M hcol i
      · intro h
        rw [extendFirstUnitary_tail]
        exact ht (Fin.succ_lt_succ_iff.mp h)
