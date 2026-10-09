-- Prove2me | solution 1 for BookProof.ChapterE3.euler_density_matrix
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:31:07.134126+00:00
-- url     : https://prove2.me/submissions/fb75b2ca-5adb-42d0-b31b-7284ce008b6b

-- Generated from ChapterE3.lean — solution of BookProof.ChapterE3.euler_density_matrix
import Mathlib
import Definitions.Def_ChapterE3
open BookProof.ChapterE3



open scoped Matrix BigOperators


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (l w : Fin n → ℝ) (θ : ℝ) :
    Matrix.vecMulVec (fun i => Real.cos θ * l i + Real.sin θ * w i)
        (fun i => Real.cos θ * l i + Real.sin θ * w i)
      = (1 / 2 : ℝ) • (Matrix.vecMulVec l l + Matrix.vecMulVec w w)
        + (Real.cos (2 * θ) / 2) • (Matrix.vecMulVec l l - Matrix.vecMulVec w w)
        + (Real.sin (2 * θ) / 2) • (Matrix.vecMulVec l w + Matrix.vecMulVec w l) := by

  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [Real.cos_two_mul, Real.sin_two_mul]
  linear_combination (w i * w j) * (Real.sin_sq_add_cos_sq θ)
