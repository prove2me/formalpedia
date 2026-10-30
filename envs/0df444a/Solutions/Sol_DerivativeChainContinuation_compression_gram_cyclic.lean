-- Prove2me | solution 1 for DerivativeChainContinuation.compression_gram_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:54:10.67309+00:00
-- url     : https://prove2.me/submissions/fba05222-3b6b-49d5-8dc1-0819f78a1345

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainContinuation_RegularizedGram
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix Polynomial
open scoped BigOperators


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open scoped BigOperators
open Matrix







theorem centeringProjection_selfAdjoint (n : ℕ) :
    (centeringProjection n).conjTranspose = centeringProjection n := by
  ext i j
  simp [centeringProjection, Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.sub_apply, Matrix.of_apply, eq_comm]

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

theorem det_scalar_add_mul_comm {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) :
    (diagonal (fun _ => t)+A*B).det=(diagonal (fun _ => t)+B*A).det := by
  have h := congrArg (fun p : Polynomial ℂ => p.eval t) (charpoly_mul_comm (-A) B)
  simpa only [eval_charpoly,neg_mul,mul_neg,sub_neg_eq_add,Matrix.scalar_apply] using h




end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution {n : ℕ} (hn : n ≠ 0) (a : Fin n → ℂ) (t : ℝ) :
    (regularizedGram (rootCompression a) t).det =
      (diagonal (fun _ => (t:ℂ))+
        diagonal (star a)*centeringProjection n*diagonal a*centeringProjection n).det := by
  let P := centeringProjection n
  let D := diagonal a
  have hp : P*P=P := centeringProjection_idempotent hn
  have hg : (rootCompression a).conjTranspose*rootCompression a =
      P*(diagonal (star a)*P*D*P) := by
    simp only [rootCompression,conjTranspose_mul,centeringProjection_selfAdjoint,diagonal_conjTranspose]
    change (P*(diagonal (star a)*P))*(P*D*P)=_
    calc
      _ = P*diagonal (star a)*(P*P)*D*P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hp]; simp only [Matrix.mul_assoc]
  rw [regularizedGram,hg,det_scalar_add_mul_comm]
  congr 2
  change (diagonal (star a)*P*D*P)*P=diagonal (star a)*P*D*P
  calc
    _ = diagonal (star a)*P*D*(P*P) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hp]
