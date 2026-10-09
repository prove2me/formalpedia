-- Prove2me | solution 1 for BookProof.ChapterConservative.timeEvo_conj_trace
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:44:05.781998+00:00
-- url     : https://prove2.me/submissions/3ba32136-991d-4df7-af0e-91b6bf708e86

-- Generated from ChapterConservative.lean — solution of BookProof.ChapterConservative.timeEvo_conj_trace
import Mathlib
import Definitions.Def_ChapterConservative
import Theorems.Thm_BookProof_ChapterConservative_timeEvo_unitary
open BookProof.ChapterConservative



open scoped Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 1000000 in
theorem solution (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ)
    (ρ : Matrix n n ℂ) :
    (timeEvo H t * ρ * (timeEvo H t)ᴴ).trace = ρ.trace := by

  rw [Matrix.trace_mul_comm]
  rw [← Matrix.mul_assoc, timeEvo_unitary H hH t, Matrix.one_mul]
