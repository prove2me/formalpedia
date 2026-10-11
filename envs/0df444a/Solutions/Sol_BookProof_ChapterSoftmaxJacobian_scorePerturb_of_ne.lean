-- Prove2me | solution 1 for BookProof.ChapterSoftmaxJacobian.scorePerturb_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:29:58.982192+00:00
-- url     : https://prove2.me/submissions/d85f1b7e-d016-4584-8b67-705e9b3a02cb

-- Generated from ChapterSoftmaxJacobian.lean — solution of BookProof.ChapterSoftmaxJacobian.scorePerturb_of_ne
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
theorem solution (s : Fin m → ℝ) {i l : Fin m} (h : l ≠ i) (t : ℝ) :
    scorePerturb s i t l = s l := by

  simp [scorePerturb, h]
