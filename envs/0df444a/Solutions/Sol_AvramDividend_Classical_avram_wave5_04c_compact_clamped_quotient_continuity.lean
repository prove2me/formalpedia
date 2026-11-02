-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_compact_clamped_quotient_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:14:55.170402+00:00
-- url     : https://prove2.me/submissions/c853a6f2-1183-415e-b124-c79e78c60c67

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Set

/-! Extend compact-domain quotient data to the unit interval by clamping. -/
theorem solution (f : ℝ → ℝ) (a : ℝ) (ha : a ≤ 1)
    (hf : ContinuousOn f (Set.Icc a 1)) :
    ContinuousOn (fun t : ℝ => f (max a (min t 1))) (Set.Icc 0 1) := by
  have hc : Continuous (fun t : ℝ => max a (min t 1)) :=
    continuous_const.max (continuous_id.min continuous_const)
  apply hf.comp hc.continuousOn
  intro t ht
  exact ⟨le_max_left _ _, max_le ha (min_le_right _ _)⟩
