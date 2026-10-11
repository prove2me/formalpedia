-- Prove2me | solution 1 for BookProof.ChapterSoftmaxSharpness.scoreSoftmax_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:43:41.028602+00:00
-- url     : https://prove2.me/submissions/23b9e628-f284-4a99-a0a8-a1a6e511fc30

-- Generated from ChapterSoftmaxSharpness.lean — solution of BookProof.ChapterSoftmaxSharpness.scoreSoftmax_zero
import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxSharpness



open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (s : Fin m → ℝ) (j : Fin m) :
    scoreSoftmax 0 s j = 1 / m := by

  simp [scoreSoftmax]
