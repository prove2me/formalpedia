-- Prove2me | solution 1 for BookProof.ChapterSoftmaxMaxEntropy.softmax_free_energy_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:33:51.740691+00:00
-- url     : https://prove2.me/submissions/8dddab7c-3897-4ea3-bd7c-11f7704cf6f4

import Definitions.Def_ChapterAttentionEntropy
import Mathlib
import Definitions.Def_ChapterSoftmaxMaxEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxFluctuation
import Theorems.Thm_BookProof_ChapterSoftmaxMaxEntropy_crossEntropy_scoreSoftmax
import Theorems.Thm_BookProof_ChapterSoftmaxMaxEntropy_shannonEntropy_le_crossEntropy
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_sum_one
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_pos
-- Generated from ChapterSoftmaxMaxEntropy.lean — theorem BookProof.ChapterSoftmaxMaxEntropy.softmax_free_energy_le
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxMaxEntropy


open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}


theorem solution (beta : ℝ) (s : Fin m → ℝ) (i : Fin m)
    {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1) :
    -logPartition beta s ≤ -(beta * ∑ j, p j * s j) - shannonEntropy p := by
  have h := BookProof.ChapterSoftmaxMaxEntropy.crossEntropy_scoreSoftmax beta s hpsum
  have h2 := BookProof.ChapterSoftmaxMaxEntropy.shannonEntropy_le_crossEntropy hp0 hpsum
    (BookProof.ChapterSoftmaxOrder.scoreSoftmax_pos beta s)
    (le_of_eq (BookProof.ChapterSoftmaxOrder.scoreSoftmax_sum_one beta s i))
  linarith

