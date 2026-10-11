-- Prove2me | solution 1 for BookProof.ChapterSoftmaxOrder.scoreSoftmax_inj_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:43:34.096884+00:00
-- url     : https://prove2.me/submissions/a8fbfcc4-ac8b-46fa-9ea5-8946f0d9d893

-- Generated from ChapterSoftmaxOrder.lean — solution of BookProof.ChapterSoftmaxOrder.scoreSoftmax_inj_iff
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
theorem solution {beta : ℝ} (hbeta : 0 < beta) (s : Fin m → ℝ) (i j : Fin m) :
    scoreSoftmax beta s i = scoreSoftmax beta s j ↔ s i = s j := by

  rw [le_antisymm_iff, le_antisymm_iff, scoreSoftmax_le_iff hbeta,
    scoreSoftmax_le_iff hbeta]
