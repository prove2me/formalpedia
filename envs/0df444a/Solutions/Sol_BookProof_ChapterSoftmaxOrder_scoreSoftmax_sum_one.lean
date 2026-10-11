-- Prove2me | solution 1 for BookProof.ChapterSoftmaxOrder.scoreSoftmax_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:33:42.205836+00:00
-- url     : https://prove2.me/submissions/1f054ea7-297a-4fd6-a2e7-ee19e34bd071

-- Generated from ChapterSoftmaxOrder.lean — solution of BookProof.ChapterSoftmaxOrder.scoreSoftmax_sum_one
import Mathlib
import Definitions.Def_ChapterSoftmaxOrder
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_denom_pos
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxOrder



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    ∑ j, scoreSoftmax beta s j = 1 := by

  simp only [scoreSoftmax]
  rw [← Finset.sum_div, div_self (scoreSoftmax_denom_pos beta s i).ne']
