-- Prove2me | solution 1 for BookProof.ChapterE3.eulerJ_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:31:21.397858+00:00
-- url     : https://prove2.me/submissions/81c73450-0448-470a-82aa-2f41f8272a24

-- Generated from ChapterE3.lean — solution of BookProof.ChapterE3.eulerJ_sq
import Mathlib
import Definitions.Def_ChapterE3
open BookProof.ChapterE3



open scoped Matrix BigOperators


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (l w : Fin n → ℝ)
    (hll : ∑ i, l i * l i = 1) (hww : ∑ i, w i * w i = 1)
    (hlw : ∑ i, l i * w i = 0) :
    eulerJ l w * eulerJ l w = - (Matrix.vecMulVec l l + Matrix.vecMulVec w w) := by

  unfold eulerJ
  -- The product of two outer products collapses to a scalar multiple of one:
  -- `(a b†)(c d†) = ⟪ b, c⟫ • (a d†)`.
  have h_mul : ∀ (a b c d : Fin n → ℝ),
      Matrix.vecMulVec a b * Matrix.vecMulVec c d = (∑ i, b i * c i) • Matrix.vecMulVec a d := by
    intro a b c d
    ext i j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hwl : ∑ i, w i * l i = 0 := by simpa [mul_comm] using hlw
  simp only [Matrix.sub_mul, Matrix.mul_sub, h_mul, hll, hww, hlw, hwl, zero_smul, one_smul]
  abel
