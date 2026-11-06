-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_negative_reserve_cutoff_continuous_compact_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:57:17.750462+00:00
-- url     : https://prove2.me/submissions/8eeb2962-3040-461d-80f6-a0c165cd21bf

import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Bounded

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
noncomputable section

/-- Continuity on nonnegative reserves and zero extension below ruin supply
a uniform bound on every state reached after a negative original jump. -/
theorem solution
    (w : ℝ → ℝ) (b : ℝ)
    (hw_cont : ContinuousOn w (Set.Ici (0 : ℝ)))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ y : ℝ, y ≤ b → |w y| ≤ R := by
  have hCont : ContinuousOn w (Set.Icc (0 : ℝ) b) :=
    hw_cont.mono (by
      intro y hy
      exact hy.1)
  obtain ⟨B, hB⟩ :=
    (CompactIccSpace.isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) b)).exists_bound_of_continuousOn hCont
  refine ⟨max B 0, le_max_right B 0, ?_⟩
  intro y hyb
  by_cases hy : y < 0
  · rw [hw_neg y hy]
    simpa only [abs_zero] using (le_max_right B 0)
  · have hy0 : 0 ≤ y := le_of_not_gt hy
    have hBound : |w y| ≤ B := by
      simpa only [Real.norm_eq_abs] using hB y ⟨hy0, hyb⟩
    exact hBound.trans (le_max_left B 0)
