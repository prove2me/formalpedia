-- Prove2me | solution 1 for BookProof.ChapterSoftmaxJacobian.softmaxJacobian_symm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:31:52.536163+00:00
-- url     : https://prove2.me/submissions/5a767f22-4530-4b33-9d24-a2d54aa9b25e

-- Generated from ChapterSoftmaxJacobian.lean — solution of BookProof.ChapterSoftmaxJacobian.softmaxJacobian_symm
import Mathlib
import Definitions.Def_ChapterSoftmaxJacobian
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxJacobian



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (i j : Fin m) :
    softmaxJacobian beta s i j = softmaxJacobian beta s j i := by

  by_cases h : j = i
  · subst h; rfl
  · simp only [softmaxJacobian, h, Ne.symm h, if_false]
    ring
