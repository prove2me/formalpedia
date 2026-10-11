-- Prove2me | solution 1 for BookProof.ChapterAttentionTopK.attendedMass_le_of_isTop
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:48:03.31319+00:00
-- url     : https://prove2.me/submissions/a641c59e-bbd4-4bf3-ba25-41009bdaab88

-- Generated from ChapterAttentionTopK.lean — solution of BookProof.ChapterAttentionTopK.attendedMass_le_of_isTop
import Mathlib
import Definitions.Def_ChapterAttentionTopK
import Theorems.Thm_BookProof_ChapterAttentionTopK_sum_le_sum_of_isTop
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_nonneg
import Definitions.Def_ChapterAttentionSparse
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterAttentionSparse
open BookProof.ChapterAttentionTopK



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) {S T : Finset (Fin m)}
    (hS : IsTop (scoreSoftmax beta s) S) (hcard : T.card ≤ S.card) :
    attendedMass beta s T ≤ attendedMass beta s S := sum_le_sum_of_isTop (scoreSoftmax_nonneg beta s) hS hcard
