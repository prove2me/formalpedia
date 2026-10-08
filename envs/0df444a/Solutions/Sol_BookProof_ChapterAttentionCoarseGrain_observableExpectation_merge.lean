-- Prove2me | solution 1 for BookProof.ChapterAttentionCoarseGrain.observableExpectation_merge
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:23:10.366491+00:00
-- url     : https://prove2.me/submissions/7369f1a1-3c42-443e-be90-b4120a26dda0

-- Generated from ChapterAttentionCoarseGrain.lean — theorem BookProof.ChapterAttentionCoarseGrain.observableExpectation_merge
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterAttentionCoarseGrain
import Definitions.Def_ChapterObservableExpectation
open BookProof.ChapterObservableExpectation
open BookProof.ChapterAttentionCoarseGrain


open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
open BookProof.ChapterSoftmaxOrder BookProof.ChapterCoherentOverlap
variable {n : ℕ}

theorem solution (f : Fin m → Fin r) (p : Fin m → ℝ) (v : Fin r → E) :
    observableExpectation (mergeWeights f p) v
      = observableExpectation p (fun x => v (f x)) := by
  have hstep : ∀ y : Fin r, mergeWeights f p y • v y
      = ∑ x ∈ Finset.univ.filter (fun x => f x = y), p x • v (f x) := by
    intro y
    rw [mergeWeights, Finset.sum_smul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [(Finset.mem_filter.mp hx).2]
  calc observableExpectation (mergeWeights f p) v
      = ∑ y, mergeWeights f p y • v y := rfl
    _ = ∑ y, ∑ x ∈ Finset.univ.filter (fun x => f x = y), p x • v (f x) :=
        Finset.sum_congr rfl fun y _ => hstep y
    _ = ∑ x, p x • v (f x) :=
        Finset.sum_fiberwise Finset.univ f (fun x => p x • v (f x))
    _ = observableExpectation p (fun x => v (f x)) := rfl

#print axioms solution

