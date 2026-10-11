-- Prove2me | solution 1 for BookProof.ChapterAttentionFactorization.prodSoftmax_marginal_right
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:45:03.978019+00:00
-- url     : https://prove2.me/submissions/1a7e91e1-2ecd-445a-98da-6b95bb16cbb4

-- Generated from ChapterAttentionFactorization.lean — solution of BookProof.ChapterAttentionFactorization.prodSoftmax_marginal_right
import Mathlib
import Definitions.Def_ChapterAttentionFactorization
import Theorems.Thm_BookProof_ChapterAttentionFactorization_prodSoftmax_apply
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_sum_one
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterAttentionFactorization



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m₁ m₂ : ℕ}

variable {m₁ m₂ : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s₁ : Fin m₁ → ℝ) (s₂ : Fin m₂ → ℝ)
    (i₁ : Fin m₁) (b : Fin m₂) :
    ∑ a, prodSoftmax beta s₁ s₂ (a, b) = scoreSoftmax beta s₂ b := by

  rw [Finset.sum_congr rfl fun a _ => prodSoftmax_apply beta s₁ s₂ a b, ← Finset.sum_mul,
    scoreSoftmax_sum_one beta s₁ i₁, one_mul]
