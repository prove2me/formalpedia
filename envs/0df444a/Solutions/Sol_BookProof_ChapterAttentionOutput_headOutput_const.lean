-- Prove2me | solution 1 for BookProof.ChapterAttentionOutput.headOutput_const
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:52:52.834296+00:00
-- url     : https://prove2.me/submissions/816e4cab-e275-4fdd-b081-d6a869d27958

import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionOutput
import Definitions.Def_ChapterSoftmaxSharpness
-- Generated from ChapterAttentionOutput.lean — theorem BookProof.ChapterAttentionOutput.headOutput_const
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionOutput


open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem solution (beta : ℝ) (s : Fin m → ℝ) (w : E) (i : Fin m) :
    headOutput beta s (fun _ => w) = w := by
  haveI : Nonempty (Fin m) := ⟨i⟩
  have hpos : 0 < ∑ l, Real.exp (beta * s l) :=
    Finset.sum_pos (fun l _ => Real.exp_pos _) Finset.univ_nonempty
  have hsum : ∑ j, scoreSoftmax beta s j = 1 := by
    unfold scoreSoftmax; rw [← Finset.sum_div]; exact div_self hpos.ne'
  unfold headOutput BookProof.ChapterObservableExpectation.observableExpectation
  rw [← Finset.sum_smul, hsum, one_smul]

