-- Prove2me | solution 1 for BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights_one
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:23:04.5125+00:00
-- url     : https://prove2.me/submissions/63beaa4f-7337-49fa-826a-2ed067d98c6a

-- Generated from ChapterAttentionCoarseGrain.lean — theorem BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights_one
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterAttentionCoarseGrain
open BookProof.ChapterAttentionCoarseGrain


open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
open BookProof.ChapterSoftmaxOrder BookProof.ChapterCoherentOverlap
variable {n : ℕ}

theorem sum_mergeWeights (f : Fin m → Fin r) (p : Fin m → ℝ) :
    ∑ y, mergeWeights f p y = ∑ x, p x :=
  Finset.sum_fiberwise Finset.univ f p

theorem solution {f : Fin m → Fin r} {p : Fin m → ℝ} (hp : ∑ x, p x = 1) :
    ∑ y, mergeWeights f p y = 1 := by
  rw [sum_mergeWeights, hp]

#print axioms solution

