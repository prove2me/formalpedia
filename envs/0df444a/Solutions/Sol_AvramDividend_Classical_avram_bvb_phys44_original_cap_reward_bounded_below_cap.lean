-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys44_original_cap_reward_bounded_below_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:49:52.176971+00:00
-- url     : https://prove2.me/submissions/91aa307e-f587-4270-aed5-e585013e0cab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
noncomputable section

/-- Compact continuity gives a uniform bound on all values below the cap. -/
theorem solution
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (c : ℝ) (hc : 0 ≤ c) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y : ℝ, y ≤ c → |w y| ≤ R := by
  have hcont : ContinuousOn w (Icc (0 : ℝ) c) :=
    hw_cont.mono (by
      intro y hy
      exact hy.1)
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) c)).exists_bound_of_continuousOn hcont
  refine ⟨max 0 M, le_max_left _ _, ?_⟩
  intro y hy
  by_cases hyneg : y < 0
  · rw [hw_neg y hyneg]
    simpa only [abs_zero] using (le_max_left (0 : ℝ) M)
  · have hmem : y ∈ Icc (0 : ℝ) c := ⟨le_of_not_gt hyneg, hy⟩
    have hbound := (hM y hmem).trans (le_max_right (0 : ℝ) M)
    simpa only [Real.norm_eq_abs] using hbound
