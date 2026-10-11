-- Prove2me | solution 1 for BookProof.ChapterSoftmaxFluctuation.varScore_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:29:49.892789+00:00
-- url     : https://prove2.me/submissions/7de3dc5c-a007-4b7d-8a5b-71348b763b0c

-- Generated from ChapterSoftmaxFluctuation.lean — solution of BookProof.ChapterSoftmaxFluctuation.varScore_nonneg
import Mathlib
import Definitions.Def_ChapterSoftmaxFluctuation
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_nonneg
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) : 0 ≤ varScore beta s :=
  Finset.sum_nonneg fun l _ =>
      mul_nonneg (scoreSoftmax_nonneg beta s l) (sq_nonneg _)
