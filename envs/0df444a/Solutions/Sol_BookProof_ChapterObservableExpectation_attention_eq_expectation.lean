-- Prove2me | solution 1 for BookProof.ChapterObservableExpectation.attention_eq_expectation
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:37:08.34282+00:00
-- url     : https://prove2.me/submissions/16f7e65d-55f5-4c14-a45e-d92336cdd7b4

-- Generated from ChapterObservableExpectation.lean — solution of BookProof.ChapterObservableExpectation.attention_eq_expectation
import Mathlib
import Definitions.Def_ChapterObservableExpectation
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
    (∀ j, 0 ≤ bornWeight q k j) ∧ (∑ j, bornWeight q k j = 1) ∧
      attentionOutput q k v = observableExpectation (bornWeight q k) v := ⟨fun j => bornWeight_nonneg q k j, bornWeight_sum_one q k j₀, rfl⟩
