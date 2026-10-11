-- Prove2me | solution 1 for BookProof.ChapterSoftmaxJacobian.scorePerturb_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:29:57.909677+00:00
-- url     : https://prove2.me/submissions/26feaea6-0e36-42b9-a309-61e8edf3c467

-- Generated from ChapterSoftmaxJacobian.lean — solution of BookProof.ChapterSoftmaxJacobian.scorePerturb_self
import Mathlib
import Definitions.Def_ChapterSoftmaxJacobian
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxJacobian



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (s : Fin m → ℝ) (i : Fin m) (t : ℝ) :
    scorePerturb s i t i = s i + t := by

  simp [scorePerturb]
