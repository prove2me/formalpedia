-- Prove2me | solution 1 for BookProof.ChapterObservableExpectation.observableExpectation_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:46:40.032143+00:00
-- url     : https://prove2.me/submissions/8d37c9a9-09d1-402a-806d-bf0bceaa7ada

-- Generated from ChapterObservableExpectation.lean — solution of BookProof.ChapterObservableExpectation.observableExpectation_norm_le
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
theorem solution {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (p : Fin m → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (v : Fin m → F) (C : ℝ) (hC : ∀ j, ‖v j‖ ≤ C) :
    ‖observableExpectation p v‖ ≤ C := by

  calc ‖observableExpectation p v‖ ≤ ∑ j, ‖p j • v j‖ := norm_sum_le _ _
    _ = ∑ j, p j * ‖v j‖ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hp j)]
    _ ≤ ∑ j, p j * C :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hC j) (hp j)
    _ = C := by rw [← Finset.sum_mul, hp1, one_mul]
