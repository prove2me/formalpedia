-- Prove2me | solution 2 for BookProof.ChapterSoftmaxMaxEntropy.softmax_free_energy_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:33:33.141644+00:00
-- url     : https://prove2.me/submissions/17966f06-12db-46b9-844b-48eb81363a7b

import Definitions.Def_ChapterAttentionEntropy
import Mathlib
import Definitions.Def_ChapterSoftmaxMaxEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxFluctuation
import Theorems.Thm_BookProof_ChapterSoftmaxMaxEntropy_crossEntropy_scoreSoftmax
import Theorems.Thm_BookProof_ChapterSoftmaxMaxEntropy_shannonEntropy_le_crossEntropy
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_sum_one
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_pos
-- Generated from ChapterSoftmaxMaxEntropy.lean — theorem BookProof.ChapterSoftmaxMaxEntropy.softmax_free_energy_eq
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxMaxEntropy


open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}


theorem solution (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    -(beta * ∑ j, scoreSoftmax beta s j * s j) - shannonEntropy (scoreSoftmax beta s)
      = -logPartition beta s := by
  have h := BookProof.ChapterSoftmaxMaxEntropy.crossEntropy_scoreSoftmax beta s
    (BookProof.ChapterSoftmaxOrder.scoreSoftmax_sum_one beta s i)
  unfold crossEntropy at h
  unfold shannonEntropy
  linarith

