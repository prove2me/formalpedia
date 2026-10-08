-- Prove2me | solution 1 for BookProof.ChapterAttentionFactorization.prodSoftmax_marginal_left
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:14:14.033978+00:00
-- url     : https://prove2.me/submissions/50cc02f3-9f06-4b2e-abcd-3c0b2da2227c

-- Generated from ChapterAttentionFactorization.lean — theorem BookProof.ChapterAttentionFactorization.prodSoftmax_marginal_left
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
    (i₂ : Fin m₂) (a : Fin m₁) :
    ∑ b, prodSoftmax beta s₁ s₂ (a, b) = scoreSoftmax beta s₁ a := by
  unfold prodSoftmax scoreSoftmax
  have hden : (∑ l : Fin m₁ × Fin m₂, Real.exp (beta * (s₁ l.1 + s₂ l.2))) =
      (∑ a, Real.exp (beta * s₁ a)) * (∑ b, Real.exp (beta * s₂ b)) := by
    simp_rw [mul_add, Real.exp_add]
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  have h₂ : (∑ b, Real.exp (beta * s₂ b)) ≠ 0 := ne_of_gt
    (Finset.sum_pos' (fun l _ => (Real.exp_pos _).le)
      ⟨i₂, Finset.mem_univ _, Real.exp_pos _⟩)
  simp_rw [hden, mul_add, Real.exp_add]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  exact mul_div_mul_right _ _ h₂

#print axioms solution

