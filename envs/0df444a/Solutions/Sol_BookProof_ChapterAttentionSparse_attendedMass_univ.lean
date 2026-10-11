-- Prove2me | solution 1 for BookProof.ChapterAttentionSparse.attendedMass_univ
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:47:29.056421+00:00
-- url     : https://prove2.me/submissions/b1e67d1d-d9e0-49ca-96d7-a08388f049ee

-- Generated from ChapterAttentionSparse.lean — solution of BookProof.ChapterAttentionSparse.attendedMass_univ
import Mathlib
import Definitions.Def_ChapterAttentionSparse
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_sum_one
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
open BookProof.ChapterAttentionSparse



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    attendedMass beta s Finset.univ = 1 := scoreSoftmax_sum_one beta s i
