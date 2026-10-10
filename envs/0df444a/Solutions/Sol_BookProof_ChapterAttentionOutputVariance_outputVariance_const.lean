-- Prove2me | solution 1 for BookProof.ChapterAttentionOutputVariance.outputVariance_const
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:45:47.897244+00:00
-- url     : https://prove2.me/submissions/84eb0307-652b-44bb-8912-0be3de6ffa63

-- Generated from ChapterAttentionOutputVariance.lean — solution of BookProof.ChapterAttentionOutputVariance.outputVariance_const
import Mathlib
import Definitions.Def_ChapterAttentionOutputVariance
import Theorems.Thm_BookProof_ChapterObservableExpectation_observableExpectation_const
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterObservableExpectation
open BookProof.ChapterAttentionOutputVariance



open scoped BigOperators RealInnerProductSpace

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (p : Fin m → ℝ) (hp : ∑ j, p j = 1) (w : E) :
    outputVariance p (fun _ => w) = 0 := by

  rw [outputVariance, observableExpectation_const p hp w]
  simp
