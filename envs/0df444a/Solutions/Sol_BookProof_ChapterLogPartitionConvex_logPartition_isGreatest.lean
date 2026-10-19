-- Prove2me | solution 1 for BookProof.ChapterLogPartitionConvex.logPartition_isGreatest
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:55:37.342993+00:00
-- url     : https://prove2.me/submissions/6c7431b6-e232-4e33-8241-04f03d7870de

import Definitions.Def_ChapterAttentionEntropy
import Mathlib
import Definitions.Def_ChapterLogPartitionConvex
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxFluctuation
import Theorems.Thm_BookProof_ChapterSoftmaxMaxEntropy_softmax_free_energy_eq
import Theorems.Thm_BookProof_ChapterSoftmaxMaxEntropy_softmax_free_energy_le
-- Generated from ChapterLogPartitionConvex.lean — theorem BookProof.ChapterLogPartitionConvex.logPartition_isGreatest
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterLogPartitionConvex


open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}


theorem solution (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    IsGreatest {x : ℝ | ∃ p : Fin m → ℝ, (∀ j, 0 ≤ p j) ∧ (∑ j, p j) = 1 ∧
        x = beta * (∑ j, p j * s j) + shannonEntropy p} (logPartition beta s) := by
  have hpos : 0 < ∑ l, Real.exp (beta * s l) :=
    Finset.sum_pos (fun l _ => Real.exp_pos _) ⟨i, Finset.mem_univ _⟩
  refine ⟨⟨scoreSoftmax beta s, fun j => ?_, ?_, ?_⟩, ?_⟩
  · unfold scoreSoftmax; positivity
  · unfold scoreSoftmax; rw [← Finset.sum_div]; exact div_self hpos.ne'
  · have := BookProof.ChapterSoftmaxMaxEntropy.softmax_free_energy_eq beta s i
    linarith
  · rintro x ⟨p, hp0, hp1, rfl⟩
    have := BookProof.ChapterSoftmaxMaxEntropy.softmax_free_energy_le beta s i hp0 hp1
    linarith

