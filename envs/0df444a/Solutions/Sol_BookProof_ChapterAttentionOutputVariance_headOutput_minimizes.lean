-- Prove2me | solution 1 for BookProof.ChapterAttentionOutputVariance.headOutput_minimizes
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:41:37.707086+00:00
-- url     : https://prove2.me/submissions/b5a49a1f-5d47-44a7-88ac-7f1938bfbbac

import Definitions.Def_ChapterObservableExpectation
import Mathlib
import Definitions.Def_ChapterAttentionOutputVariance
import Definitions.Def_ChapterSoftmaxSharpness
-- Generated from ChapterAttentionOutputVariance.lean — theorem BookProof.ChapterAttentionOutputVariance.headOutput_minimizes
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionOutputVariance


open scoped BigOperators RealInnerProductSpace

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionOutput

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
theorem solution (beta : ℝ) (s : Fin m → ℝ) (v : Fin m → E) (i : Fin m) (c : E) :
    ∑ j, scoreSoftmax beta s j * ‖v j - headOutput beta s v‖ ^ 2
      ≤ ∑ j, scoreSoftmax beta s j * ‖v j - c‖ ^ 2 := by
  set p := scoreSoftmax beta s with hpdef
  set μ := headOutput beta s v with hμ
  have hS : 0 < ∑ l, Real.exp (beta * s l) :=
    Finset.sum_pos (fun l _ => Real.exp_pos _) ⟨i, Finset.mem_univ _⟩
  have hp1 : ∑ j, p j = 1 := by
    rw [hpdef]; unfold scoreSoftmax; rw [← Finset.sum_div, div_self hS.ne']
  have hμdef : μ = ∑ j, p j • v j := rfl
  have hcenter : ∑ j, p j • (v j - μ) = 0 := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hp1, one_smul, ← hμdef, sub_self]
  have hexp : ∀ j, ‖v j - c‖ ^ 2 = ‖v j - μ‖ ^ 2 + 2 * inner ℝ (v j - μ) (μ - c) + ‖μ - c‖ ^ 2 := by
    intro j
    have := norm_add_sq_real (v j - μ) (μ - c)
    rw [show v j - μ + (μ - c) = v j - c by abel] at this
    exact this
  have hcross : ∑ j, p j * inner ℝ (v j - μ) (μ - c) = 0 := by
    have : inner ℝ (∑ j, p j • (v j - μ)) (μ - c) = 0 := by rw [hcenter, inner_zero_left]
    rw [sum_inner] at this
    simpa [real_inner_smul_left] using this
  simp_rw [hexp, mul_add, Finset.sum_add_distrib]
  have h2 : ∑ j, p j * (2 * inner ℝ (v j - μ) (μ - c)) = 0 := by
    have : ∑ j, p j * (2 * inner ℝ (v j - μ) (μ - c)) = 2 * ∑ j, p j * inner ℝ (v j - μ) (μ - c) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
    rw [this, hcross, mul_zero]
  rw [h2, add_zero, ← Finset.sum_mul, hp1, one_mul]
  have := sq_nonneg ‖μ - c‖
  linarith
