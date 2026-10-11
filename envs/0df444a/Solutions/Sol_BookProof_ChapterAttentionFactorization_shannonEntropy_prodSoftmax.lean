-- Prove2me | solution 1 for BookProof.ChapterAttentionFactorization.shannonEntropy_prodSoftmax
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:45:05.19157+00:00
-- url     : https://prove2.me/submissions/8e021886-fd19-41b2-b728-e943fe0f27eb

-- Generated from ChapterAttentionFactorization.lean — solution of BookProof.ChapterAttentionFactorization.shannonEntropy_prodSoftmax
import Mathlib
import Definitions.Def_ChapterAttentionFactorization
import Theorems.Thm_BookProof_ChapterAttentionFactorization_prodSoftmax_apply
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_pos
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_sum_one
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterAttentionEntropy
open BookProof.ChapterAttentionFactorization



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m₁ m₂ : ℕ}

variable {m₁ m₂ : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s₁ : Fin m₁ → ℝ) (s₂ : Fin m₂ → ℝ)
    (i₁ : Fin m₁) (i₂ : Fin m₂) :
    shannonEntropyProd (prodSoftmax beta s₁ s₂)
      = shannonEntropy (scoreSoftmax beta s₁) + shannonEntropy (scoreSoftmax beta s₂) := by

  have h₁ : ∑ a, scoreSoftmax beta s₁ a = 1 := scoreSoftmax_sum_one beta s₁ i₁
  have h₂ : ∑ b, scoreSoftmax beta s₂ b = 1 := scoreSoftmax_sum_one beta s₂ i₂
  have hterm : ∀ (a : Fin m₁) (b : Fin m₂),
      prodSoftmax beta s₁ s₂ (a, b) * Real.log (prodSoftmax beta s₁ s₂ (a, b))
        = (scoreSoftmax beta s₁ a * Real.log (scoreSoftmax beta s₁ a)) * scoreSoftmax beta s₂ b
          + scoreSoftmax beta s₁ a
            * (scoreSoftmax beta s₂ b * Real.log (scoreSoftmax beta s₂ b)) := by
    intro a b
    rw [prodSoftmax_apply, Real.log_mul (ne_of_gt (scoreSoftmax_pos beta s₁ a))
      (ne_of_gt (scoreSoftmax_pos beta s₂ b))]
    ring
  have hrow : ∀ a : Fin m₁,
      ∑ b, prodSoftmax beta s₁ s₂ (a, b) * Real.log (prodSoftmax beta s₁ s₂ (a, b))
        = scoreSoftmax beta s₁ a * Real.log (scoreSoftmax beta s₁ a)
          + scoreSoftmax beta s₁ a
            * ∑ b, scoreSoftmax beta s₂ b * Real.log (scoreSoftmax beta s₂ b) := by
    intro a
    rw [Finset.sum_congr rfl fun b _ => hterm a b, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, h₂, mul_one]
  rw [shannonEntropyProd, Fintype.sum_prod_type, Finset.sum_congr rfl fun a _ => hrow a,
    Finset.sum_add_distrib, ← Finset.sum_mul, h₁, one_mul, shannonEntropy, shannonEntropy]
  ring
