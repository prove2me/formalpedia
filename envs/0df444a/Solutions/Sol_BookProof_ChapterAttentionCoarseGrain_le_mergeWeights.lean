-- Prove2me | solution 1 for BookProof.ChapterAttentionCoarseGrain.le_mergeWeights
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:23:06.366699+00:00
-- url     : https://prove2.me/submissions/895ccd41-7cc3-442b-8d48-345b42f47df9

-- Generated from ChapterAttentionCoarseGrain.lean — theorem BookProof.ChapterAttentionCoarseGrain.le_mergeWeights
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

theorem solution {f : Fin m → Fin r} {p : Fin m → ℝ} (hp : ∀ x, 0 ≤ p x) (x : Fin m) :
    p x ≤ mergeWeights f p (f x) := by
  refine Finset.single_le_sum (f := p) (fun z _ => hp z) ?_
  simp

#print axioms solution

