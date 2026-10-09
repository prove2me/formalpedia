-- Prove2me | solution 1 for BookProof.ChapterAttentionOutputVariance.sum_dist_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:32:08.185924+00:00
-- url     : https://prove2.me/submissions/0c0de354-5a6d-4134-b756-8817d151e13a

-- Generated from ChapterAttentionOutputVariance.lean — solution of BookProof.ChapterAttentionOutputVariance.sum_dist_sq_eq
import Mathlib
import Definitions.Def_ChapterAttentionOutputVariance
import Theorems.Thm_BookProof_ChapterAttentionOutputVariance_sum_dist_sq_expand
open BookProof.ChapterAttentionOutputVariance



open scoped BigOperators RealInnerProductSpace

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {p : Fin m → ℝ} (hp : ∑ j, p j = 1) (v : Fin m → E) (c : E) :
    ∑ j, p j * ‖v j - c‖ ^ 2
      = outputVariance p v + ‖observableExpectation p v - c‖ ^ 2 := by

  have h1 := sum_dist_sq_expand hp v c
  have h2 := sum_dist_sq_expand hp v (observableExpectation p v)
  have h3 : ⟪observableExpectation p v, observableExpectation p v⟫
      = ‖observableExpectation p v‖ ^ 2 := real_inner_self_eq_norm_sq _
  have h4 : ‖observableExpectation p v - c‖ ^ 2
      = ‖observableExpectation p v‖ ^ 2 - 2 * ⟪observableExpectation p v, c⟫ + ‖c‖ ^ 2 :=
    norm_sub_sq_real _ _
  rw [h1, outputVariance, h2, h3, h4]
  ring
