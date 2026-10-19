-- Prove2me | solution 1 for BookProof.ChapterSoftmaxMaxEntropy.shannonEntropy_scoreSoftmax
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:33:19.571796+00:00
-- url     : https://prove2.me/submissions/6eeaa1e4-1d96-4fe6-b942-65e38d4799ee

import Definitions.Def_ChapterAttentionEntropy
import Mathlib
import Definitions.Def_ChapterSoftmaxMaxEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxFluctuation
import Theorems.Thm_BookProof_ChapterSoftmaxMaxEntropy_crossEntropy_scoreSoftmax
import Theorems.Thm_BookProof_ChapterSoftmaxMaxEntropy_shannonEntropy_le_crossEntropy
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_sum_one
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_pos
-- Generated from ChapterSoftmaxMaxEntropy.lean — theorem BookProof.ChapterSoftmaxMaxEntropy.shannonEntropy_scoreSoftmax
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxMaxEntropy


open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}


theorem solution (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    shannonEntropy (scoreSoftmax beta s) = logPartition beta s - beta * meanScore beta s := by
  have h := BookProof.ChapterSoftmaxMaxEntropy.crossEntropy_scoreSoftmax beta s
    (BookProof.ChapterSoftmaxOrder.scoreSoftmax_sum_one beta s i)
  unfold crossEntropy at h
  unfold shannonEntropy meanScore
  exact h

