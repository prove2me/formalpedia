-- Prove2me | solution 1 for BookProof.ChapterEulerGenericDensity.conditional_probability_at
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:50:11.411216+00:00
-- url     : https://prove2.me/submissions/d45b5cf8-e64e-476d-8bf1-29f762fc6b1b

-- Generated from ChapterEulerGenericDensity.lean — solution of BookProof.ChapterEulerGenericDensity.conditional_probability_at
import Mathlib
import Definitions.Def_ChapterEulerGenericDensity
open BookProof.ChapterEulerGenericDensity



open scoped Matrix
open Matrix


variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℝ) (l w : Fin d → ℝ)
    (k : Fin d) (hlk : l k = 1) (hwk : w k = 0) :
    ((Real.cos θ ^ 2) • Matrix.vecMulVec l l
      + (Real.sin θ ^ 2) • Matrix.vecMulVec w w) k k = Real.cos θ ^ 2 := by

  simp [Matrix.vecMulVec_apply, smul_eq_mul, hlk, hwk]
