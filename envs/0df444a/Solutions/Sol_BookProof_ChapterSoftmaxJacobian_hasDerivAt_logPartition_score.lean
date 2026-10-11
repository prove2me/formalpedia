-- Prove2me | solution 1 for BookProof.ChapterSoftmaxJacobian.hasDerivAt_logPartition_score
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:30:03.247042+00:00
-- url     : https://prove2.me/submissions/fca3b3cf-b955-40fe-ac73-5a728502801b

-- Generated from ChapterSoftmaxJacobian.lean — solution of BookProof.ChapterSoftmaxJacobian.hasDerivAt_logPartition_score
import Mathlib
import Definitions.Def_ChapterSoftmaxJacobian
import Theorems.Thm_BookProof_ChapterSoftmaxJacobian_hasDerivAt_partition_score
import Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_partition_ne_zero
import Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_scoreSoftmax_eq_div
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
    HasDerivAt (fun t : ℝ => logPartition beta (scorePerturb s i t))
      (beta * scoreSoftmax beta s i) 0 := by
  have hne := partition_ne_zero beta s i
  have h := (hasDerivAt_partition_score beta s i).log (by simpa using hne)
  refine h.congr_deriv ?_
  rw [scoreSoftmax_eq_div]
  simp [mul_div_assoc]
