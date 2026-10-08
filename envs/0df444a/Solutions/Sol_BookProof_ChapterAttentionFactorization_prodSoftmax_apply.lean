-- Prove2me | solution 1 for BookProof.ChapterAttentionFactorization.prodSoftmax_apply
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:14:08.020877+00:00
-- url     : https://prove2.me/submissions/49487ed5-15fc-4794-9b91-9142214634b7

-- Generated from ChapterAttentionFactorization.lean — theorem BookProof.ChapterAttentionFactorization.prodSoftmax_apply
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionFactorization
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionFactorization


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m₁ m₂ : ℕ}

theorem solution (beta : ℝ) (s₁ : Fin m₁ → ℝ) (s₂ : Fin m₂ → ℝ)
    (a : Fin m₁) (b : Fin m₂) :
    prodSoftmax beta s₁ s₂ (a, b) = scoreSoftmax beta s₁ a * scoreSoftmax beta s₂ b := by
  unfold prodSoftmax scoreSoftmax
  have hden : (∑ l : Fin m₁ × Fin m₂, Real.exp (beta * (s₁ l.1 + s₂ l.2))) =
      (∑ a, Real.exp (beta * s₁ a)) * (∑ b, Real.exp (beta * s₂ b)) := by
    simp_rw [mul_add, Real.exp_add]
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  rw [hden, mul_add, Real.exp_add, mul_div_mul_comm]

#print axioms solution

