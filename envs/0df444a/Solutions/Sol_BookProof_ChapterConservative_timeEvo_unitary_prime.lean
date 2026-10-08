-- Prove2me | solution 1 for BookProof.ChapterConservative.timeEvo_unitary_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T14:06:45.989016+00:00
-- url     : https://prove2.me/submissions/648380f2-a69d-464b-9be5-3768a791f5cc

-- Generated from ChapterConservative.lean — solution of BookProof.ChapterConservative.timeEvo_unitary'
import Mathlib
import Definitions.Def_ChapterConservative
import Theorems.Thm_BookProof_ChapterConservative_timeEvo_unitary
open BookProof.ChapterConservative



open scoped Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 1000000 in
theorem solution (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ) :
    (timeEvo H t) * (timeEvo H t)ᴴ = 1 := by

  rw [← mul_eq_one_comm, timeEvo_unitary]
  exact hH
