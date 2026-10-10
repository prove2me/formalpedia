-- Prove2me | solution 1 for BookProof.ChapterLpRestrictSplit.orthogonalFamily_splitEmbed
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:25:48.663889+00:00
-- url     : https://prove2.me/submissions/22a48f7c-88bf-4a2b-8e22-a4b2dfdbe697

-- Generated from ChapterLpRestrictSplit.lean — solution of BookProof.ChapterLpRestrictSplit.orthogonalFamily_splitEmbed
import Mathlib
import Definitions.Def_ChapterLpRestrictSplit
import Theorems.Thm_BookProof_ChapterLpRestrictSplit_inner_restrictEmbed_eq_zero
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLpRestrictSplit



noncomputable section

open MeasureTheory


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {mu : Measure α}

variable {α : Type*} [MeasurableSpace α] {mu : Measure α}

set_option maxHeartbeats 1000000 in
theorem solution {A : Set α} (hA : MeasurableSet A) :
    OrthogonalFamily ℂ (fun b : Bool => Lp ℂ 2 (mu.restrict (splitSet A b)))
      (splitEmbed hA) := by

  intro i j hij u v
  have hdisj : Disjoint (splitSet A i) (splitSet A j) := by
    cases i <;> cases j <;> simp_all [splitSet, disjoint_compl_left, disjoint_compl_right]
  exact inner_restrictEmbed_eq_zero _ _ hdisj u v
