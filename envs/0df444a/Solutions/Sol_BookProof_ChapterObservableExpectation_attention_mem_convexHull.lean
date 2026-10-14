-- Prove2me | solution 1 for BookProof.ChapterObservableExpectation.attention_mem_convexHull
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:37:09.430652+00:00
-- url     : https://prove2.me/submissions/e8b6fb1b-4c99-4bdd-bf51-3a9078f57a0b

-- Generated from ChapterObservableExpectation.lean — solution of BookProof.ChapterObservableExpectation.attention_mem_convexHull
import Mathlib
import Definitions.Def_ChapterObservableExpectation
import Theorems.Thm_BookProof_ChapterObservableExpectation_prob_weighted_sum_mem_convexHull
import Theorems.Thm_BookProof_ChapterSoftmaxBorn_bornWeight_nonneg
import Theorems.Thm_BookProof_ChapterSoftmaxBorn_bornWeight_sum_one
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
theorem solution (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (v : Fin m → E) (j₀ : Fin m) :
    attentionOutput q k v ∈ convexHull ℝ (Set.range v) :=
  prob_weighted_sum_mem_convexHull _ (fun j => bornWeight_nonneg q k j)
      (bornWeight_sum_one q k j₀) v
