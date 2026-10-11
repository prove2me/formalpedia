-- Prove2me | solution 1 for BookProof.ChapterAttentionTopK.isTopWeight_of_isTopScore
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:48:04.459625+00:00
-- url     : https://prove2.me/submissions/fa6830ec-c83d-4129-a90c-d02eaf3d2a49

-- Generated from ChapterAttentionTopK.lean — solution of BookProof.ChapterAttentionTopK.isTopWeight_of_isTopScore
import Mathlib
import Definitions.Def_ChapterAttentionTopK
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_le_iff
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterAttentionTopK



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {beta : ℝ} (hbeta : 0 < beta) (s : Fin m → ℝ)
    {S : Finset (Fin m)} (hS : ∀ x ∈ S, ∀ y ∉ S, s y ≤ s x) :
    IsTop (scoreSoftmax beta s) S :=
  fun x hx y hy =>
    (scoreSoftmax_le_iff hbeta s y x).2 (hS x hx y hy)
