-- Prove2me | solution 1 for BookProof.ChapterConservative.timeEvo_inv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:43:40.396564+00:00
-- url     : https://prove2.me/submissions/dd437364-cebd-4254-8a11-d659c28fee6c

-- Generated from ChapterConservative.lean — solution of BookProof.ChapterConservative.timeEvo_inv
import Mathlib
import Definitions.Def_ChapterConservative
import Theorems.Thm_BookProof_ChapterConservative_timeEvo_zero
import Theorems.Thm_BookProof_ChapterConservative_timeEvo_add
open BookProof.ChapterConservative



open scoped Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 1000000 in
theorem solution (H : Matrix n n ℂ) (t : ℝ) :
    timeEvo H t * timeEvo H (-t) = 1 := by

  convert timeEvo_add H t (-t) using 1
  simp [timeEvo_zero]
