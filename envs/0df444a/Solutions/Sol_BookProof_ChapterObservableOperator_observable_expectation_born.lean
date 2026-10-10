-- Prove2me | solution 1 for BookProof.ChapterObservableOperator.observable_expectation_born
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:46:52.833339+00:00
-- url     : https://prove2.me/submissions/7ea7d125-c535-4bff-a8ba-04923cedb9f3

-- Generated from ChapterObservableOperator.lean — solution of BookProof.ChapterObservableOperator.observable_expectation_born
import Mathlib
import Definitions.Def_ChapterObservableOperator
import Theorems.Thm_BookProof_ChapterObservableOperator_bornProb_nonneg
import Theorems.Thm_BookProof_ChapterObservableOperator_observableOp_expectation
import Theorems.Thm_BookProof_ChapterObservableOperator_bornProb_sum_one
import Theorems.Thm_BookProof_ChapterObservableExpectation_observableExpectation_scalar
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterObservableExpectation
open BookProof.ChapterObservableOperator



open scoped BigOperators

noncomputable section


variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (b : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin n)))
    (v : Fin m → ℝ) (q : EuclideanSpace ℂ (Fin n)) (hq : ‖q‖ = 1) :
    (∀ j, 0 ≤ bornProb (fun j => b j) q j) ∧
      (∑ j, bornProb (fun j => b j) q j = 1) ∧
      expectation (observableOp (fun j => b j) v) q
        = ((∑ j, bornProb (fun j => b j) q j * v j : ℝ) : ℂ) :=
  ⟨fun j => bornProb_nonneg _ q j, bornProb_sum_one b q hq, by
      rw [observableOp_expectation,
        BookProof.ChapterObservableExpectation.observableExpectation_scalar]⟩
