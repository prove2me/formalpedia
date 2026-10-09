-- Prove2me | solution 1 for BookProof.ChapterAttentionOutputVariance.norm_observableExpectation_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:32:33.408566+00:00
-- url     : https://prove2.me/submissions/bf1a5cc2-a8f3-486a-9fa5-de5dbfb45f83

-- Generated from ChapterAttentionOutputVariance.lean — solution of BookProof.ChapterAttentionOutputVariance.norm_observableExpectation_sq_le
import Mathlib
import Definitions.Def_ChapterAttentionOutputVariance
import Theorems.Thm_BookProof_ChapterAttentionOutputVariance_outputVariance_nonneg
import Theorems.Thm_BookProof_ChapterAttentionOutputVariance_outputVariance_eq_sub
open BookProof.ChapterAttentionOutputVariance



open scoped BigOperators RealInnerProductSpace

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j)
    (hp : ∑ j, p j = 1) (v : Fin m → E) :
    ‖observableExpectation p v‖ ^ 2 ≤ ∑ j, p j * ‖v j‖ ^ 2 := by

  have h := outputVariance_eq_sub hp v
  have hv := outputVariance_nonneg hp0 v
  linarith
