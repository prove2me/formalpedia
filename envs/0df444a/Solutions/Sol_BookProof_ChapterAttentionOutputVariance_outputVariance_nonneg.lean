-- Prove2me | solution 1 for BookProof.ChapterAttentionOutputVariance.outputVariance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:31:43.715168+00:00
-- url     : https://prove2.me/submissions/e0ac2314-01cd-4ac6-9138-a09fc4b6f6b1

-- Generated from ChapterAttentionOutputVariance.lean — solution of BookProof.ChapterAttentionOutputVariance.outputVariance_nonneg
import Mathlib
import Definitions.Def_ChapterAttentionOutputVariance
open BookProof.ChapterAttentionOutputVariance



open scoped BigOperators RealInnerProductSpace

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {p : Fin m → ℝ} (hp0 : ∀ j, 0 ≤ p j) (v : Fin m → E) :
    0 ≤ outputVariance p v := Finset.sum_nonneg fun j _ => mul_nonneg (hp0 j) (sq_nonneg _)
