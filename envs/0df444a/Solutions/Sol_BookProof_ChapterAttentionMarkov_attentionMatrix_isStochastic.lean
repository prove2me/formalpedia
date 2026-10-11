-- Prove2me | solution 1 for BookProof.ChapterAttentionMarkov.attentionMatrix_isStochastic
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:45:09.440977+00:00
-- url     : https://prove2.me/submissions/28fa36c5-0740-4dd3-8cc4-3ad13bc6d486

-- Generated from ChapterAttentionMarkov.lean — solution of BookProof.ChapterAttentionMarkov.attentionMatrix_isStochastic
import Mathlib
import Definitions.Def_ChapterAttentionMarkov
import Theorems.Thm_BookProof_ChapterAttentionMarkov_attentionMatrix_pos
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_sum_one
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
open BookProof.ChapterAttentionMarkov



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (S : Fin m → Fin m → ℝ) :
    IsStochastic (attentionMatrix beta S) :=
  ⟨fun i j => (attentionMatrix_pos beta S i j).le,
      fun i => scoreSoftmax_sum_one beta (S i) i⟩
