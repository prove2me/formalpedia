-- Prove2me | solution 1 for BookProof.ChapterAttentionRetrieval.card_erase_cast
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:37:59.989643+00:00
-- url     : https://prove2.me/submissions/2ce7fdaa-8a48-43d0-a8e5-6d7f234f05a1

-- Generated from ChapterAttentionRetrieval.lean — solution of BookProof.ChapterAttentionRetrieval.card_erase_cast
import Mathlib
import Definitions.Def_ChapterAttentionRetrieval
open BookProof.ChapterAttentionRetrieval



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (j : Fin m) :
    ((Finset.univ.erase j).card : ℝ) = (m : ℝ) - 1 := by

  have hm : 1 ≤ m := j.pos
  rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
    Nat.cast_sub hm, Nat.cast_one]
