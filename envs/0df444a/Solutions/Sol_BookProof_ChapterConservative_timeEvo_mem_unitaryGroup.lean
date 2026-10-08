-- Prove2me | solution 1 for BookProof.ChapterConservative.timeEvo_mem_unitaryGroup
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:30:51.256335+00:00
-- url     : https://prove2.me/submissions/7631ceed-6609-40f4-b3de-a143a88879a1

-- Generated from ChapterConservative.lean — solution of BookProof.ChapterConservative.timeEvo_mem_unitaryGroup
import Mathlib
import Definitions.Def_ChapterConservative
import Theorems.Thm_BookProof_ChapterConservative_timeEvo_unitary
import Theorems.Thm_BookProof_ChapterConservative_timeEvo_unitary_prime
open BookProof.ChapterConservative



open scoped Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 1000000 in
theorem solution (H : Matrix n n ℂ) (hH : H.IsHermitian) (t : ℝ) :
    timeEvo H t ∈ Matrix.unitaryGroup n ℂ := by

  constructor
  · convert timeEvo_unitary H hH t using 1
    rw [Matrix.star_eq_conjTranspose]
  · convert timeEvo_unitary_prime H hH t using 1
    rw [Matrix.star_eq_conjTranspose]
