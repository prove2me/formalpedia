-- Prove2me | solution 1 for BookProof.ChapterConservative.timeEvo_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T14:13:04.31298+00:00
-- url     : https://prove2.me/submissions/ceb3800e-b2a8-4eba-80d9-30b10f4d5ccf

-- Generated from ChapterConservative.lean — solution of BookProof.ChapterConservative.timeEvo_add
import Mathlib
import Definitions.Def_ChapterConservative
import Theorems.Thm_BookProof_ChapterConservative_timeEvo_commute
open BookProof.ChapterConservative



open scoped Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 1000000 in
theorem solution (H : Matrix n n ℂ) (s t : ℝ) :
    timeEvo H s * timeEvo H t = timeEvo H (s + t) := by

  unfold timeEvo
  rw [← Matrix.exp_add_of_commute]
  · simp [add_smul]
  · exact timeEvo_commute H s t
