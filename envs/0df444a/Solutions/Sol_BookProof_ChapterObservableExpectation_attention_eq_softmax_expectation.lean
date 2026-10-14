-- Prove2me | solution 1 for BookProof.ChapterObservableExpectation.attention_eq_softmax_expectation
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:37:10.534142+00:00
-- url     : https://prove2.me/submissions/d46895ec-a998-4e0e-8dd6-ce1776fbda1b

-- Generated from ChapterObservableExpectation.lean — solution of BookProof.ChapterObservableExpectation.attention_eq_softmax_expectation
import Mathlib
import Definitions.Def_ChapterObservableExpectation
import Theorems.Thm_BookProof_ChapterSoftmaxBorn_coherentBorn_eq_softmax
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
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r)
    (v : Fin m → E) :
    attentionOutput q k v = observableExpectation (softmax 2 q k) v := by

  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coherentBorn_eq_softmax q k r hk j]
