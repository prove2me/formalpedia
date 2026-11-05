-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_public_nonzero_finite_marks_positive_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:49:30.963374+00:00
-- url     : https://prove2.me/submissions/91ca2d98-205b-467f-9247-2ccf72416218

import Mathlib.Data.Finset.Insert
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- A finite set of nonzero actual marks has one positive magnitude cut-off. -/
theorem solution
    {ι : Type*} (S : Finset ι) (j : ι → ℝ)
    (hS : ∀ i ∈ S, j i ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ S, δ ≤ |j i| := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨1, by norm_num, ?_⟩
      simp
  | @insert a s ha ih =>
      have hne : j a ≠ 0 := hS a (Finset.mem_insert_self a s)
      have hs : ∀ i ∈ s, j i ≠ 0 := by
        intro i hi
        exact hS i (Finset.mem_insert_of_mem hi)
      obtain ⟨δ, hδ, hbound⟩ := ih hs
      refine ⟨min δ (|j a|), lt_min hδ (abs_pos.mpr hne), ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hbound i hi)
