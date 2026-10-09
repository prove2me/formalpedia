-- Prove2me | solution 1 for BookProof.ChapterAttentionSparse.maskedSoftmax_sub_of_mem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:41:07.889142+00:00
-- url     : https://prove2.me/submissions/de429e1d-49d2-4fc6-820d-2df7b7e09ecc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterAttentionSparse.lean — solution of BookProof.ChapterAttentionSparse.maskedSoftmax_sub_of_mem
import Mathlib
import Definitions.Def_ChapterAttentionSparse
import Theorems.Thm_BookProof_ChapterAttentionSparse_attendedMass_pos
import Theorems.Thm_BookProof_ChapterAttentionMasking_maskedSoftmax_eq_conditional
import Definitions.Def_ChapterAttentionMasking
open BookProof.ChapterAttentionMasking
open BookProof.ChapterAttentionSparse



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)}
    {j : Fin m} (hj : j ∈ S) :
    maskedSoftmax beta s S j - scoreSoftmax beta s j
      = scoreSoftmax beta s j * (1 - attendedMass beta s S) / attendedMass beta s S := by

  have hP : 0 < attendedMass beta s S := attendedMass_pos beta s ⟨j, hj⟩
  rw [maskedSoftmax_eq_conditional beta s hj, ← attendedMass]
  field_simp
