-- Prove2me | solution 1 for BookProof.ChapterConservative.timeEvo_commute
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T14:06:43.16199+00:00
-- url     : https://prove2.me/submissions/149f94d2-d371-47b5-bb07-74ef08fbf853

-- Generated from ChapterConservative.lean — solution of BookProof.ChapterConservative.timeEvo_commute
import Mathlib
import Definitions.Def_ChapterConservative
open BookProof.ChapterConservative



open scoped Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 1000000 in
theorem solution (H : Matrix n n ℂ) (s t : ℝ) :
    Commute ((s : ℂ) • (Complex.I • H)) ((t : ℂ) • (Complex.I • H)) := by

  ext i j; simp [ mul_left_comm ]
