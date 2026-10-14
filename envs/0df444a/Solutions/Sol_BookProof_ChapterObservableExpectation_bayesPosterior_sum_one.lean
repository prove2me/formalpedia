-- Prove2me | solution 1 for BookProof.ChapterObservableExpectation.bayesPosterior_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T11:39:00.900546+00:00
-- url     : https://prove2.me/submissions/955a05fe-465e-49e7-b2a3-cb7f0192f286

-- Generated from ChapterObservableExpectation.lean — theorem BookProof.ChapterObservableExpectation.bayesPosterior_sum_one
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference
open BookProof.ChapterObservableExpectation


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn

variable {m n : ℕ}
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

variable {Y : Type*}
open BookProof.ChapterObservableExpectation

theorem solution{prior : Fin m → ℝ} {L : Fin m → Y → ℝ} (y : Y)
    (hy : 0 < evidence prior L y) : ∑ x, posterior prior L y x = 1 := by
  unfold posterior
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (by unfold evidence at hy; exact hy))
