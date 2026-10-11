-- Prove2me | solution 1 for BookProof.ChapterSoftmaxOrder.scoreSoftmax_argmax
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:43:35.071906+00:00
-- url     : https://prove2.me/submissions/4d345cac-f74d-47bc-8e32-ee453dfc8eaa

-- Generated from ChapterSoftmaxOrder.lean — solution of BookProof.ChapterSoftmaxOrder.scoreSoftmax_argmax
import Mathlib
import Definitions.Def_ChapterSoftmaxOrder
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_le_iff
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxOrder



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {beta : ℝ} (hbeta : 0 < beta) (s : Fin m → ℝ) (j : Fin m)
    (hj : ∀ l, s l ≤ s j) (i : Fin m) :
    scoreSoftmax beta s i ≤ scoreSoftmax beta s j := (scoreSoftmax_le_iff hbeta s i j).2 (hj i)
