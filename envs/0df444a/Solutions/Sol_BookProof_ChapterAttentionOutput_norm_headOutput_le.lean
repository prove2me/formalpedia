-- Prove2me | solution 1 for BookProof.ChapterAttentionOutput.norm_headOutput_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:36:09.524985+00:00
-- url     : https://prove2.me/submissions/a6162e10-9531-40c5-823b-5425837e386e

import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionOutput
import Definitions.Def_ChapterSoftmaxSharpness
-- Generated from ChapterAttentionOutput.lean — theorem BookProof.ChapterAttentionOutput.norm_headOutput_le
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionOutput


open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
open BookProof.ChapterSoftmaxSharpness BookProof.ChapterAttentionOutput in
theorem h44_head {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nonempty (Fin m)]
    (beta : ℝ) (s : Fin m → ℝ) {v : Fin m → E} {C : ℝ} (hv : ∀ j, ‖v j‖ ≤ C) :
    ‖headOutput beta s v‖ ≤ C := by
  have hpos : 0 < ∑ l, Real.exp (beta * s l) :=
    Finset.sum_pos (fun l _ => Real.exp_pos _) Finset.univ_nonempty
  have hw : ∀ j, 0 ≤ scoreSoftmax beta s j := fun j => by
    unfold scoreSoftmax; positivity
  have hsum : ∑ j, scoreSoftmax beta s j = 1 := by
    unfold scoreSoftmax; rw [← Finset.sum_div]; exact div_self hpos.ne'
  unfold headOutput BookProof.ChapterObservableExpectation.observableExpectation
  calc ‖∑ j, scoreSoftmax beta s j • v j‖ ≤ ∑ j, ‖scoreSoftmax beta s j • v j‖ := norm_sum_le _ _
    _ = ∑ j, scoreSoftmax beta s j * ‖v j‖ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw j)]
    _ ≤ ∑ j, scoreSoftmax beta s j * C := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hv j) (hw j)
    _ = C := by rw [← Finset.sum_mul, hsum, one_mul]

theorem solution (beta : ℝ) (s : Fin m → ℝ) {v : Fin m → E} {C : ℝ}
    (hv : ∀ j, ‖v j‖ ≤ C) (i : Fin m) : ‖headOutput beta s v‖ ≤ C := by
  haveI : Nonempty (Fin m) := ⟨i⟩
  exact h44_head beta s hv

