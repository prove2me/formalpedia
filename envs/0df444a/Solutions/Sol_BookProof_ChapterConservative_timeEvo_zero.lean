-- Prove2me | solution 1 for BookProof.ChapterConservative.timeEvo_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T14:06:41.676021+00:00
-- url     : https://prove2.me/submissions/0b630b38-86aa-4d25-8017-59f31a134606

-- Generated from ChapterConservative.lean — solution of BookProof.ChapterConservative.timeEvo_zero
import Mathlib
import Definitions.Def_ChapterConservative
open BookProof.ChapterConservative



open scoped Matrix


variable {n : Type*} [Fintype n] [DecidableEq n]

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 1000000 in
theorem solution (H : Matrix n n ℂ) : timeEvo H 0 = 1 := by

  unfold timeEvo; aesop
