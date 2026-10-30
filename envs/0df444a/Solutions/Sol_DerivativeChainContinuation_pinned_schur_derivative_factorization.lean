-- Prove2me | solution 1 for DerivativeChainContinuation.pinned_schur_derivative_factorization
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:52:38.714608+00:00
-- url     : https://prove2.me/submissions/1b3396c3-dd08-4827-9eaf-f0c2c531ba77

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainContinuation_PolynomialMoments
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_constant_unitary_compression
import Theorems.Thm_DerivativeChainContinuation_diagonal_projection_charpoly
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open scoped BigOperators
open Matrix









theorem centeringProjection_idempotent {n : ℕ} (hn : n ≠ 0) :
    centeringProjection n * centeringProjection n = centeringProjection n := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  unfold centeringProjection
  simp only [sub_mul, mul_sub, one_mul, mul_one]
  have he : (Matrix.of (fun _ _ : Fin n => (n : ℂ)⁻¹)) * (Matrix.of (fun _ _ : Fin n => (n : ℂ)⁻¹)) =
      (Matrix.of (fun _ _ : Fin n => (n : ℂ)⁻¹)) := by
    ext i j
    simp [Matrix.mul_apply, hnC]
  rw [he]
  abel







end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix Polynomial
open scoped BigOperators



theorem rootCompression_charpoly {n : ℕ} (hn : n ≠ 0) (a : Fin n → ℂ) :
    (rootCompression a).charpoly =
      C (n : ℂ)⁻¹ * X * derivative (∏ i, (X-C (a i))) := by
  rw [rootCompression, charpoly_mul_comm, ← Matrix.mul_assoc,
    centeringProjection_idempotent hn, charpoly_mul_comm,
    diagonal_projection_charpoly hn]

end DerivativeChainContinuation


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix Polynomial
open scoped BigOperators



theorem charpoly_unitary_conjugate {n : ℕ} (M U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ unitaryGroup (Fin n) ℂ) :
    (U.conjTranspose*M*U).charpoly = M.charpoly := by
  have hUU : U*U.conjTranspose = 1 := mem_unitaryGroup_iff.mp hU
  rw [charpoly_mul_comm, ← Matrix.mul_assoc, hUU, one_mul]





end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (n : ℕ) (a : Fin (n+1) → ℂ)
    (Q : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hQ : Q ∈ unitaryGroup (Fin (n+1)) ℂ)
    (hfirst : ∀ i, Q i 0=((Real.sqrt (n+1:ℝ))⁻¹:ℂ))
    (ht : (Q.conjTranspose*rootCompression a*Q).IsUpperTriangular) :
    monicDerivative (∏ i, (X-C (a i))) =
      ∏ j : Fin n, (X-C ((Q.conjTranspose*diagonal a*Q) j.succ j.succ)) := by
  have hc := charpoly_unitary_conjugate (rootCompression a) Q hQ
  rw [charpoly_of_isUpperTriangular _ ht, rootCompression_charpoly (by omega)] at hc
  have hzero : (Q.conjTranspose*rootCompression a*Q) 0 0=0 := by
    rw [constant_unitary_compression n a Q hQ hfirst]
    simp [Matrix.mul_apply,Matrix.diagonal_apply]
  have htail (j : Fin n) : (Q.conjTranspose*rootCompression a*Q) j.succ j.succ =
      (Q.conjTranspose*diagonal a*Q) j.succ j.succ := by
    rw [constant_unitary_compression n a Q hQ hfirst]
    simp [Matrix.mul_apply,Matrix.diagonal_apply]
  rw [Fin.prod_univ_succ,hzero,C_0,sub_zero] at hc
  simp only [htail] at hc
  have hd : (∏ i, (X-C (a i))).natDegree=n+1 := by simp
  have hr : C ((n+1:ℕ):ℂ)⁻¹*X*derivative (∏ i, (X-C (a i))) =
      X*monicDerivative (∏ i, (X-C (a i))) := by
    rw [monicDerivative,hd]
    push_cast
    ring
  rw [hr] at hc
  exact mul_left_cancel₀ X_ne_zero hc.symm
