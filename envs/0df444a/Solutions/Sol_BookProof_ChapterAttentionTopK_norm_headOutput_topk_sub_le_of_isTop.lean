-- Prove2me | solution 1 for BookProof.ChapterAttentionTopK.norm_headOutput_topk_sub_le_of_isTop
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T22:58:30.629903+00:00
-- url     : https://prove2.me/submissions/208488d4-bf4b-4da9-a701-0d4d415d1468

-- Generated from ChapterAttentionTopK.lean — solution of BookProof.ChapterAttentionTopK.norm_headOutput_topk_sub_le_of_isTop
import Mathlib
import Definitions.Def_ChapterAttentionTopK
import Theorems.Thm_BookProof_ChapterAttentionTopK_attendedMass_le_of_isTop
import Theorems.Thm_BookProof_ChapterAttentionSparse_norm_headOutput_masked_sub_le
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterAttentionMasking
import Definitions.Def_ChapterAttentionOutput
import Definitions.Def_ChapterAttentionSparse
import Theorems.Thm_BookProof_ChapterAttentionSparse_norm_headOutput_masked_sub_le
open BookProof.ChapterAttentionTopK
-- attendedMass + norm_headOutput_masked_sub_le live in AttentionSparse, whose
-- published Def bundle carries `attendedMass` but not an `open` here
open BookProof.ChapterAttentionSparse



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterObservableExpectation
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionMasking
open BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in

theorem solution (beta : ℝ) (s : Fin m → ℝ)
    {S T : Finset (Fin m)} (hS : IsTop (scoreSoftmax beta s) S) (hcard : T.card ≤ S.card)
    (hSne : S.Nonempty) (i : Fin m) {v : Fin m → E} {C : ℝ} (hv : ∀ j, ‖v j‖ ≤ C)
    (hC : 0 ≤ C) :
    ‖observableExpectation (maskedSoftmax beta s S) v - headOutput beta s v‖
      ≤ 2 * (1 - attendedMass beta s T) * C := by
  refine le_trans (norm_headOutput_masked_sub_le beta s hSne i hv) ?_
  have := attendedMass_le_of_isTop beta s hS hcard
  have h2 : 2 * (1 - attendedMass beta s S) ≤ 2 * (1 - attendedMass beta s T) := by linarith
  exact mul_le_mul_of_nonneg_right h2 hC
