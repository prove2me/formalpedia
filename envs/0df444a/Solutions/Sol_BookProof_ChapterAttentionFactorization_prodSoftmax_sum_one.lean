-- Prove2me | solution 1 for BookProof.ChapterAttentionFactorization.prodSoftmax_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:14:11.91274+00:00
-- url     : https://prove2.me/submissions/0ae04a35-c39b-4f56-8256-a364d37f3c06

-- Generated from ChapterAttentionFactorization.lean — theorem BookProof.ChapterAttentionFactorization.prodSoftmax_sum_one
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
    (i₁ : Fin m₁) (i₂ : Fin m₂) : ∑ j : Fin m₁ × Fin m₂, prodSoftmax beta s₁ s₂ j = 1 := by
  unfold prodSoftmax
  rw [← Finset.sum_div]
  apply div_self
  apply ne_of_gt
  exact Finset.sum_pos' (fun l _ => (Real.exp_pos _).le)
    ⟨(i₁, i₂), Finset.mem_univ _, Real.exp_pos _⟩

#print axioms solution

