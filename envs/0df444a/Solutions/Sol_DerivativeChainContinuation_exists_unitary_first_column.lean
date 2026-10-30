-- Prove2me | solution 1 for DerivativeChainContinuation.exists_unitary_first_column
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T18:19:42.592931+00:00
-- url     : https://prove2.me/submissions/2a241626-2afb-44e6-84c3-96e55d6ea061

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_exists_first_eigenvector_basis
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


open DerivativeChainContinuation in
theorem solution (n : ℕ)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    ∃ Q : Matrix (Fin (n+1)) (Fin (n+1)) ℂ,
      Q ∈ unitaryGroup (Fin (n+1)) ℂ ∧
      ∀ i : Fin n, (Q.conjTranspose*A*Q) i.succ 0 = 0 := by
  obtain ⟨μ, b, hb⟩ := exists_first_eigenvector_basis n A
  let e := EuclideanSpace.basisFun (Fin (n+1)) ℂ
  let Q := e.toBasis.toMatrix b.toBasis
  have hQ : Q ∈ unitaryGroup (Fin (n+1)) ℂ :=
    e.toMatrix_orthonormalBasis_mem_unitary b
  have hback : b.toBasis.toMatrix e.toBasis = Q.conjTranspose := by
    have hQQ : Q*Q.conjTranspose = 1 := e.toMatrix_orthonormalBasis_self_mul_conjTranspose b
    calc
      b.toBasis.toMatrix e.toBasis = b.toBasis.toMatrix e.toBasis*(Q*Q.conjTranspose) := by rw [hQQ, mul_one]
      _ = (b.toBasis.toMatrix e.toBasis*Q)*Q.conjTranspose := by rw [Matrix.mul_assoc]
      _ = Q.conjTranspose := by
        have hh := Module.Basis.toMatrix_mul_toMatrix_flip b.toBasis e.toBasis
        exact (congrArg (fun T => T*Q.conjTranspose) hh).trans (one_mul _)
  have hA : LinearMap.toMatrix e.toBasis e.toBasis A.toEuclideanLin = A := by
    rw [toEuclideanLin_eq_toLin_orthonormal]
    exact LinearMap.toMatrix_toLin _ _ _
  have hM := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    b.toBasis e.toBasis b.toBasis e.toBasis A.toEuclideanLin
  rw [hA, hback] at hM
  refine ⟨Q, hQ, fun i => ?_⟩
  rw [hM]
  simp [LinearMap.toMatrix_apply, hb, map_smul, Module.Basis.repr_self,
    Finsupp.single_apply, Fin.succ_ne_zero]
