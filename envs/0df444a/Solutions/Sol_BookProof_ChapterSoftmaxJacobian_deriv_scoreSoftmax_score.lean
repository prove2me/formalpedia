-- Prove2me | solution 1 for BookProof.ChapterSoftmaxJacobian.deriv_scoreSoftmax_score
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:31:38.838989+00:00
-- url     : https://prove2.me/submissions/cf134d05-dff1-48b5-afad-59ae18f09e6e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSoftmaxJacobian.lean — solution of BookProof.ChapterSoftmaxJacobian.deriv_scoreSoftmax_score
import Mathlib
import Definitions.Def_ChapterSoftmaxJacobian
import Theorems.Thm_BookProof_ChapterSoftmaxJacobian_hasDerivAt_scoreSoftmax_score
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
    deriv (fun t : ℝ => scoreSoftmax beta (scorePerturb s i t) j) 0
      = softmaxJacobian beta s i j := (hasDerivAt_scoreSoftmax_score beta s i j).deriv
