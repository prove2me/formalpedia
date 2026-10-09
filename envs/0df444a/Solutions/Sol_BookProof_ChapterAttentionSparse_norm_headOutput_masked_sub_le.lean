-- Prove2me | solution 1 for BookProof.ChapterAttentionSparse.norm_headOutput_masked_sub_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T18:41:57.514882+00:00
-- url     : https://prove2.me/submissions/c62990fa-a52f-4c60-b1ac-aa2c1301e866
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterAttentionSparse.lean — solution of BookProof.ChapterAttentionSparse.norm_headOutput_masked_sub_le
import Mathlib
import Definitions.Def_ChapterAttentionSparse
import Theorems.Thm_BookProof_ChapterAttentionSparse_l1dist_maskedSoftmax_eq
import Theorems.Thm_BookProof_ChapterAttentionOutput_norm_observableExpectation_sub_le
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterAttentionMasking
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterAttentionOutput
open BookProof.ChapterAttentionMasking
open BookProof.ChapterObservableExpectation
open BookProof.ChapterAttentionSparse



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) {S : Finset (Fin m)}
    (hS : S.Nonempty) (i : Fin m) {v : Fin m → E} {C : ℝ} (hv : ∀ j, ‖v j‖ ≤ C) :
    ‖observableExpectation (maskedSoftmax beta s S) v - headOutput beta s v‖
      ≤ 2 * (1 - attendedMass beta s S) * C := by

  have h := norm_observableExpectation_sub_le (E := E) (maskedSoftmax beta s S)
    (scoreSoftmax beta s) hv
  have hl1 : (∑ j, |maskedSoftmax beta s S j - scoreSoftmax beta s j|)
      = 2 * (1 - attendedMass beta s S) := l1dist_maskedSoftmax_eq beta s hS i
  rw [hl1] at h
  exact h
