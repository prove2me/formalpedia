-- Prove2me | solution 1 for BookProof.ChapterSoftmaxFluctuation.varScore_eq_sub_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:29:48.882356+00:00
-- url     : https://prove2.me/submissions/435c25ad-34ef-4428-8880-6a25b266c301

-- Generated from ChapterSoftmaxFluctuation.lean — solution of BookProof.ChapterSoftmaxFluctuation.varScore_eq_sub_sq
import Mathlib
import Definitions.Def_ChapterSoftmaxFluctuation
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_sum_one
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    varScore beta s = (∑ l, scoreSoftmax beta s l * s l ^ 2) - meanScore beta s ^ 2 := by

  have hsum : ∑ l, scoreSoftmax beta s l = 1 := scoreSoftmax_sum_one beta s i
  have hexp : ∀ l : Fin m, scoreSoftmax beta s l * (s l - meanScore beta s) ^ 2
      = scoreSoftmax beta s l * s l ^ 2
        - 2 * meanScore beta s * (scoreSoftmax beta s l * s l)
        + meanScore beta s ^ 2 * scoreSoftmax beta s l := by
    intro l; ring
  rw [varScore, Finset.sum_congr rfl fun l _ => hexp l, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum, ← meanScore]
  ring
