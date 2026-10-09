-- Prove2me | solution 1 for BookProof.ChapterAttentionOutput.norm_observableExpectation_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:31:42.629594+00:00
-- url     : https://prove2.me/submissions/22ff2e65-feff-4568-80be-2207c60c1749

-- Generated from ChapterAttentionOutput.lean — solution of BookProof.ChapterAttentionOutput.norm_observableExpectation_sub_le
import Mathlib
import Definitions.Def_ChapterAttentionOutput
import Definitions.Def_ChapterObservableExpectation
open BookProof.ChapterObservableExpectation
open BookProof.ChapterAttentionOutput



open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (p q : Fin m → ℝ) {v : Fin m → E} {C : ℝ}
    (hv : ∀ j, ‖v j‖ ≤ C) :
    ‖observableExpectation p v - observableExpectation q v‖ ≤ (∑ j, |p j - q j|) * C := by

  have hdiff : observableExpectation p v - observableExpectation q v
      = ∑ j, (p j - q j) • v j := by
    rw [observableExpectation, observableExpectation, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [sub_smul]
  calc ‖observableExpectation p v - observableExpectation q v‖
      ≤ ∑ j, ‖(p j - q j) • v j‖ := by rw [hdiff]; exact norm_sum_le _ _
    _ = ∑ j, |p j - q j| * ‖v j‖ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ j, |p j - q j| * C := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _)
    _ = (∑ j, |p j - q j|) * C := by rw [Finset.sum_mul]
