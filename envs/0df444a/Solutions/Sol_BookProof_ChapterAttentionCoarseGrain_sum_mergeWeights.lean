-- Prove2me | solution 1 for BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:23:02.502995+00:00
-- url     : https://prove2.me/submissions/989026f3-f60b-45c3-9f45-bebc8de91b7c

-- Generated from ChapterAttentionCoarseGrain.lean — theorem BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights
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

theorem solution (f : Fin m → Fin r) (p : Fin m → ℝ) :
    ∑ y, mergeWeights f p y = ∑ x, p x :=
  Finset.sum_fiberwise Finset.univ f p

#print axioms solution

