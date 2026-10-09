-- Prove2me | solution 1 for BookProof.ChapterEulerGenericDensity.vecMulVec_mul_vecMulVec
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:47:51.262976+00:00
-- url     : https://prove2.me/submissions/92f90397-0512-45ee-b2c1-d530921dbebc

-- Generated from ChapterEulerGenericDensity.lean — solution of BookProof.ChapterEulerGenericDensity.vecMulVec_mul_vecMulVec
import Mathlib
import Definitions.Def_ChapterEulerGenericDensity
open BookProof.ChapterEulerGenericDensity



open scoped Matrix
open Matrix


variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (u v x y : Fin d → ℝ) :
    Matrix.vecMulVec u v * Matrix.vecMulVec x y = (v ⬝ᵥ x) • Matrix.vecMulVec u y := by

  ext i k
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, dotProduct,
    smul_eq_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro j _; ring
