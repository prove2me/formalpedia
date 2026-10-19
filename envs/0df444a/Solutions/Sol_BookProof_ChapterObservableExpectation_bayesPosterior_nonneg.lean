-- Prove2me | solution 1 for BookProof.ChapterObservableExpectation.bayesPosterior_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:40:59.709434+00:00
-- url     : https://prove2.me/submissions/d4a1970c-6f38-49cd-b45d-fd4be42cdb02

-- Generated from ChapterObservableExpectation.lean — solution of BookProof.ChapterObservableExpectation.bayesPosterior_nonneg
import Mathlib
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterBayesInference
import Definitions.Def_ChapterDeepLearningSampling
open BookProof.ChapterObservableExpectation



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn
open BookProof.ChapterBayesInference
open BookProof.ChapterDeepLearningSampling

variable {m n : ℕ}
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

variable {m n : ℕ}
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {Y : Type*}

set_option maxHeartbeats 1000000 in

theorem solution {prior : Fin m → ℝ} {L : Fin m → Y → ℝ}
    (hprior : ∀ x, 0 ≤ prior x) (hL : ∀ x y, 0 ≤ L x y) (y : Y) (x : Fin m) :
    0 ≤ posterior prior L y x :=
  div_nonneg (mul_nonneg (hprior x) (hL x y))
    (Finset.sum_nonneg fun _ _ => mul_nonneg (hprior _) (hL _ _))
