-- Prove2me | solution 1 for BookProof.ChapterObservableExpectation.prob_weighted_sum_mem_convexHull
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:46:38.683874+00:00
-- url     : https://prove2.me/submissions/628168b3-1b86-4e3c-bfc1-df34be6cd16f

-- Generated from ChapterObservableExpectation.lean — solution of BookProof.ChapterObservableExpectation.prob_weighted_sum_mem_convexHull
import Mathlib
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterObservableExpectation



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn

variable {m n : ℕ}
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

variable {m n : ℕ}
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (p : Fin m → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hp1 : ∑ j, p j = 1) (v : Fin m → E) :
    observableExpectation p v ∈ convexHull ℝ (Set.range v) := by

  refine (convex_convexHull ℝ (Set.range v)).sum_mem (fun j _ => hp j) hp1 ?_
  intro j _
  exact subset_convexHull ℝ (Set.range v) ⟨j, rfl⟩
