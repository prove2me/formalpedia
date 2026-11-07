-- Prove2me | solution 1 for AvramDividend.Classical.avram_f15_continuous_zero_negative_uniform_bounded_above
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T08:46:37.900147+00:00
-- url     : https://prove2.me/submissions/b22e2caa-1f2f-42f0-9acf-0f1839103d85

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
noncomputable section

theorem solution
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Set.Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (K : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, y ≤ K → |w y| ≤ B := by
  let I : Set ℝ := Icc 0 (max 0 K)
  have hIcompact : IsCompact I := by
    exact isCompact_Icc
  have hInonempty : I.Nonempty := by
    refine ⟨0, ?_⟩
    simp [I]
  have hwI : ContinuousOn w I := by
    apply hw_cont.mono
    intro y hy
    exact hy.1
  have hIabs : ContinuousOn (fun y => |w y|) I := hwI.abs
  obtain ⟨z, hz, hzmax⟩ :=
    hIcompact.exists_isMaxOn hInonempty hIabs
  refine ⟨max 0 |w z|, le_max_left _ _, ?_⟩
  intro y hyK
  by_cases hy0 : y < 0
  · rw [hw_neg y hy0]
    simpa using (le_max_left (0 : ℝ) |w z|)
  · have hy_nonneg : 0 ≤ y := le_of_not_gt hy0
    have hyI : y ∈ I := ⟨hy_nonneg, hyK.trans (le_max_right 0 K)⟩
    exact (hzmax hyI).trans (le_max_right _ _)
