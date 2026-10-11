-- Prove2me | solution 1 for BookProof.ChapterSoftmaxOrder.scoreSoftmax_pos
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:33:40.361353+00:00
-- url     : https://prove2.me/submissions/34f816ea-fe9f-4c5c-9da1-dafe1d255204

-- Generated from ChapterSoftmaxOrder.lean — solution of BookProof.ChapterSoftmaxOrder.scoreSoftmax_pos
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
theorem solution (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    0 < scoreSoftmax beta s j := div_pos (Real.exp_pos _) (scoreSoftmax_denom_pos beta s j)
