-- Prove2me | solution 1 for DerivativeChainContinuation.extendFirstUnitary_mem
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T18:21:42.107911+00:00
-- url     : https://prove2.me/submissions/8c96257a-7552-42dd-8ae3-ae3421027793

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SchurExtension
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000


open DerivativeChainContinuation in
theorem solution {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ unitaryGroup (Fin n) ℂ) :
    extendFirstUnitary U ∈ unitaryGroup (Fin (n+1)) ℂ := by
  rw [mem_unitaryGroup_iff'] at hU ⊢
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j
  · simp [extendFirstUnitary, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, Matrix.one_apply, eq_comm]
  · simp [extendFirstUnitary, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, Matrix.one_apply, eq_comm]
  · simp [extendFirstUnitary, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, Matrix.one_apply, eq_comm]
  · have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hU
    simpa [extendFirstUnitary, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, Matrix.one_apply, eq_comm] using h
