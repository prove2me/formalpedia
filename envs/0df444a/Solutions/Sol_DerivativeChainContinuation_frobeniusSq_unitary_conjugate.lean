-- Prove2me | solution 1 for DerivativeChainContinuation.frobeniusSq_unitary_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T18:26:54.66732+00:00
-- url     : https://prove2.me/submissions/1dd5f8bd-1526-4029-9e46-23e10a286242

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix
open scoped BigOperators

theorem frobeniusSq_trace {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    (frobeniusSq M : ℂ) = (M.conjTranspose*M).trace := by
  simp only [frobeniusSq, Complex.ofReal_sum, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Complex.normSq_eq_conj_mul_self]
  exact Finset.sum_comm



end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution {n : ℕ} (M U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ unitaryGroup (Fin n) ℂ) :
    frobeniusSq (U.conjTranspose*M*U) = frobeniusSq M := by
  apply Complex.ofReal_injective
  rw [frobeniusSq_trace, frobeniusSq_trace]
  have hUU : U*U.conjTranspose = 1 := (mem_unitaryGroup_iff.mp hU : U*star U=1)
  calc
    ((U.conjTranspose*M*U).conjTranspose*(U.conjTranspose*M*U)).trace =
      (U.conjTranspose*(M.conjTranspose*(U*U.conjTranspose)*M)*U).trace := by
        congr 1
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = (U.conjTranspose*(M.conjTranspose*M)*U).trace := by rw [hUU, mul_one]
    _ = (U*U.conjTranspose*(M.conjTranspose*M)).trace := by
      rw [Matrix.trace_mul_cycle]
    _ = (M.conjTranspose*M).trace := by rw [hUU, one_mul]
