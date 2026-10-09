-- Prove2me | solution 1 for BookProof.ChapterAttentionOutputVariance.observableExpectation_minimizes
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:32:20.042815+00:00
-- url     : https://prove2.me/submissions/0f3b6c0b-f751-43ce-a577-ea72f69f1206

-- Generated from ChapterAttentionOutputVariance.lean — solution of BookProof.ChapterAttentionOutputVariance.observableExpectation_minimizes
import Mathlib
import Definitions.Def_ChapterAttentionOutputVariance
import Theorems.Thm_BookProof_ChapterAttentionOutputVariance_sum_dist_sq_eq
open BookProof.ChapterAttentionOutputVariance



open scoped BigOperators RealInnerProductSpace

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {p : Fin m → ℝ} (hp : ∑ j, p j = 1) (v : Fin m → E)
    (c : E) :
    ∑ j, p j * ‖v j - observableExpectation p v‖ ^ 2 ≤ ∑ j, p j * ‖v j - c‖ ^ 2 := by

  rw [sum_dist_sq_eq hp v c, ← outputVariance]
  nlinarith [sq_nonneg ‖observableExpectation p v - c‖]
