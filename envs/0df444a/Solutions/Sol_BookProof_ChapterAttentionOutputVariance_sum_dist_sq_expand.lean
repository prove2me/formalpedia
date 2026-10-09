-- Prove2me | solution 1 for BookProof.ChapterAttentionOutputVariance.sum_dist_sq_expand
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:31:55.724607+00:00
-- url     : https://prove2.me/submissions/0576026b-883b-4942-86d7-6808c8faaff1

-- Generated from ChapterAttentionOutputVariance.lean — solution of BookProof.ChapterAttentionOutputVariance.sum_dist_sq_expand
import Mathlib
import Definitions.Def_ChapterAttentionOutputVariance
open BookProof.ChapterAttentionOutputVariance



open scoped BigOperators RealInnerProductSpace

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {p : Fin m → ℝ} (hp : ∑ j, p j = 1) (v : Fin m → E) (c : E) :
    ∑ j, p j * ‖v j - c‖ ^ 2
      = (∑ j, p j * ‖v j‖ ^ 2) - 2 * ⟪observableExpectation p v, c⟫ + ‖c‖ ^ 2 := by

  have hexp : ∀ j : Fin m, p j * ‖v j - c‖ ^ 2
      = p j * ‖v j‖ ^ 2 - 2 * (p j * ⟪v j, c⟫) + p j * ‖c‖ ^ 2 := by
    intro j
    rw [@norm_sub_sq_real]
    ring
  have hinner : ⟪observableExpectation p v, c⟫ = ∑ j, p j * ⟪v j, c⟫ := by
    rw [observableExpectation, sum_inner]
    exact Finset.sum_congr rfl fun j _ => real_inner_smul_left _ _ _
  rw [Finset.sum_congr rfl fun j _ => hexp j]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hp,
    one_mul, hinner]
