-- Prove2me | solution 1 for DerivativeChainContinuation.regularizedGram_first_blocks
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:22:22.551987+00:00
-- url     : https://prove2.me/submissions/f65ccd7d-79a1-4270-8e4a-cf36e8c1672b

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FirstGramBlock
import Definitions.Def_DerivativeChainContinuation_RegularizedGram
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
open scoped BigOperators


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Matrix
open scoped BigOperators



@[simp] theorem firstSumEquiv_left (n : ℕ) (i : Unit) : firstSumEquiv n (.inl i)=0 := by
  cases i
  simp [firstSumEquiv]

@[simp] theorem firstSumEquiv_right (n : ℕ) (j : Fin n) : firstSumEquiv n (.inr j)=j.succ := by
  simp [firstSumEquiv]


end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (n : ℕ) (T : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hcol : ∀ i : Fin n,T i.succ 0=0) (t : ℝ) :
    (regularizedGram T t).submatrix (firstSumEquiv n) (firstSumEquiv n) =
      fromBlocks
        (Matrix.of (fun _ _ : Unit => (t:ℂ)+(Complex.normSq (T 0 0):ℂ)))
        (Matrix.of (fun (_ : Unit) (j : Fin n) => star (T 0 0)*T 0 j.succ))
        (Matrix.of (fun (i : Fin n) (_ : Unit) => star (T 0 i.succ)*T 0 0))
        (regularizedGram (T.submatrix Fin.succ Fin.succ) t+
          vecMulVec (fun i => star (T 0 i.succ)) (fun j => T 0 j.succ)) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp [regularizedGram,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_succ,
        hcol,Matrix.diagonal_apply,Complex.normSq_eq_conj_mul_self,Complex.star_def]
    | inr j =>
      simp [regularizedGram,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_succ,
        hcol,Matrix.diagonal_apply,eq_comm]
  | inr i =>
    cases j with
    | inl j =>
      simp [regularizedGram,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_succ,
        hcol,Matrix.diagonal_apply,eq_comm]
    | inr j =>
      simp [regularizedGram,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_succ,
        Matrix.diagonal_apply,Matrix.vecMulVec_apply,Matrix.submatrix_apply,add_assoc,add_comm,add_left_comm]
