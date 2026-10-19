-- Prove2me | solution 1 for BookProof.ChapterSoftmaxMaxEntropy.shannonEntropy_le_of_meanScore_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:34:18.351824+00:00
-- url     : https://prove2.me/submissions/d5c5508f-5d74-40eb-a52b-ce29b9a5121c

import Definitions.Def_ChapterAttentionEntropy
import Mathlib
import Definitions.Def_ChapterSoftmaxMaxEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxFluctuation
import Theorems.Thm_BookProof_ChapterSoftmaxMaxEntropy_crossEntropy_scoreSoftmax
import Theorems.Thm_BookProof_ChapterSoftmaxMaxEntropy_shannonEntropy_le_crossEntropy
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_sum_one
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_pos
-- Generated from ChapterSoftmaxMaxEntropy.lean — theorem BookProof.ChapterSoftmaxMaxEntropy.shannonEntropy_le_of_meanScore_eq
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxMaxEntropy


open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}


theorem solution (beta : ℝ) (s : Fin m → ℝ) (i : Fin m)
    {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1)
    (hmean : ∑ j, p j * s j = meanScore beta s) :
    shannonEntropy p ≤ shannonEntropy (scoreSoftmax beta s) := by
  have h := BookProof.ChapterSoftmaxMaxEntropy.crossEntropy_scoreSoftmax beta s hpsum
  have h2 := BookProof.ChapterSoftmaxMaxEntropy.shannonEntropy_le_crossEntropy hp0 hpsum
    (BookProof.ChapterSoftmaxOrder.scoreSoftmax_pos beta s)
    (le_of_eq (BookProof.ChapterSoftmaxOrder.scoreSoftmax_sum_one beta s i))
  have h3 := BookProof.ChapterSoftmaxMaxEntropy.crossEntropy_scoreSoftmax beta s
    (BookProof.ChapterSoftmaxOrder.scoreSoftmax_sum_one beta s i)
  unfold crossEntropy at h3
  have h4 : shannonEntropy (scoreSoftmax beta s) = logPartition beta s - beta * meanScore beta s := by
    unfold shannonEntropy meanScore
    exact h3
  rw [h4, ← hmean]
  linarith

