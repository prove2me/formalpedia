-- Prove2me | solution 1 for BookProof.ChapterAttentionFactorization.prodSoftmax_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:13:37.613988+00:00
-- url     : https://prove2.me/submissions/4a29ec86-60b1-4929-8d63-8c4f9a80ee65

-- Generated from ChapterAttentionFactorization.lean — theorem BookProof.ChapterAttentionFactorization.prodSoftmax_eq_mul
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
    (j : Fin m₁ × Fin m₂) :
    prodSoftmax beta s₁ s₂ j = scoreSoftmax beta s₁ j.1 * scoreSoftmax beta s₂ j.2 := by
  unfold prodSoftmax scoreSoftmax
  have hden : (∑ l : Fin m₁ × Fin m₂, Real.exp (beta * (s₁ l.1 + s₂ l.2))) =
      (∑ a, Real.exp (beta * s₁ a)) * (∑ b, Real.exp (beta * s₂ b)) := by
    simp_rw [mul_add, Real.exp_add]
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  rw [hden, mul_add, Real.exp_add, mul_div_mul_comm]

#print axioms solution

