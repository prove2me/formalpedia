-- Prove2me | solution 1 for BookProof.ChapterEulerGenericDensity.Jgen_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:48:30.150031+00:00
-- url     : https://prove2.me/submissions/41b674c8-43b7-4c30-a836-5df17b61cd7e

-- Generated from ChapterEulerGenericDensity.lean — solution of BookProof.ChapterEulerGenericDensity.Jgen_sq
import Mathlib
import Definitions.Def_ChapterEulerGenericDensity
import Theorems.Thm_BookProof_ChapterEulerGenericDensity_vecMulVec_mul_vecMulVec
open BookProof.ChapterEulerGenericDensity



open scoped Matrix
open Matrix


variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (l w : Fin d → ℝ)
    (hll : l ⬝ᵥ l = 1) (hww : w ⬝ᵥ w = 1) (hlw : l ⬝ᵥ w = 0) :
    Jgen l w * Jgen l w = -(Matrix.vecMulVec l l + Matrix.vecMulVec w w) := by

  have hwl : w ⬝ᵥ l = 0 := by rw [dotProduct_comm]; exact hlw
  simp only [Jgen, sub_mul, mul_sub, vecMulVec_mul_vecMulVec, hll, hww, hlw, hwl,
    one_smul, zero_smul]
  abel
