-- Prove2me | solution 1 for BookProof.ChapterSoftmaxJacobian.deriv_logPartition_score
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:31:24.90608+00:00
-- url     : https://prove2.me/submissions/ba9778d8-fe0b-40c5-9e30-300eda24725d

-- Generated from ChapterSoftmaxJacobian.lean — solution of BookProof.ChapterSoftmaxJacobian.deriv_logPartition_score
import Mathlib
import Definitions.Def_ChapterSoftmaxJacobian
import Theorems.Thm_BookProof_ChapterSoftmaxJacobian_hasDerivAt_logPartition_score
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterSoftmaxJacobian



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    deriv (fun t : ℝ => logPartition beta (scorePerturb s i t)) 0
      = beta * scoreSoftmax beta s i :=
  (hasDerivAt_logPartition_score beta s i).deriv

/-! ## The Jacobian of Softmax -/
