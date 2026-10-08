-- Prove2me | solution 1 for BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights_log
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:23:08.113984+00:00
-- url     : https://prove2.me/submissions/f2794ed0-9ce4-46b9-b202-6453d61d85df

-- Generated from ChapterAttentionCoarseGrain.lean — theorem BookProof.ChapterAttentionCoarseGrain.sum_mergeWeights_log
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
    ∑ y, mergeWeights f p y * Real.log (mergeWeights f p y)
      = ∑ x, p x * Real.log (mergeWeights f p (f x)) := by
  have hstep : ∀ y : Fin r, mergeWeights f p y * Real.log (mergeWeights f p y)
      = ∑ x ∈ Finset.univ.filter (fun x => f x = y),
          p x * Real.log (mergeWeights f p (f x)) := by
    intro y
    have h1 : ∑ x ∈ Finset.univ.filter (fun x => f x = y),
          p x * Real.log (mergeWeights f p (f x))
        = ∑ x ∈ Finset.univ.filter (fun x => f x = y), p x * Real.log (mergeWeights f p y) :=
      Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2]
    rw [h1, ← Finset.sum_mul]
    rfl
  calc ∑ y, mergeWeights f p y * Real.log (mergeWeights f p y)
      = ∑ y, ∑ x ∈ Finset.univ.filter (fun x => f x = y),
          p x * Real.log (mergeWeights f p (f x)) :=
        Finset.sum_congr rfl fun y _ => hstep y
    _ = ∑ x, p x * Real.log (mergeWeights f p (f x)) :=
        Finset.sum_fiberwise Finset.univ f
          (fun x => p x * Real.log (mergeWeights f p (f x)))

#print axioms solution

