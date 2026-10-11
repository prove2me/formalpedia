-- Prove2me | solution 1 for BookProof.ChapterObservableOperator.observableOp_expectation_mem_convexHull
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:57:31.892996+00:00
-- url     : https://prove2.me/submissions/04eb4b40-158f-40d6-955c-70a3a6750438

-- Generated from ChapterObservableOperator.lean — solution of BookProof.ChapterObservableOperator.observableOp_expectation_mem_convexHull
import Mathlib
import Definitions.Def_ChapterObservableOperator
import Theorems.Thm_BookProof_ChapterObservableOperator_bornProb_nonneg
import Theorems.Thm_BookProof_ChapterObservableOperator_bornProb_sum_one
import Theorems.Thm_BookProof_ChapterObservableExpectation_prob_weighted_sum_mem_convexHull
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterObservableExpectation
open BookProof.ChapterObservableOperator



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution
    (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin n))) (v : Fin m → ℝ)
    (q : EuclideanSpace ℂ (Fin n)) (hq : ‖q‖ = 1) :
    BookProof.ChapterObservableExpectation.observableExpectation
        (bornProb (fun j => b j) q) v ∈ convexHull ℝ (Set.range v) :=
  BookProof.ChapterObservableExpectation.prob_weighted_sum_mem_convexHull _
      (fun j => bornProb_nonneg _ q j) (bornProb_sum_one b q hq) v
