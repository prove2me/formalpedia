-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_continuous_unit_interval_profile
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:19:37.585349+00:00
-- url     : https://prove2.me/submissions/28d41b87-1c55-43c4-b388-b048fd7ea10c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Set

/-! Lift the compactified jump profile into the Bernstein-domain C space. -/
theorem solution (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1)) :
    ∃ G : C(unitInterval.Elem, ℝ),
      ∀ t : unitInterval.Elem, G t = f (t : ℝ) := by
  have hc : Continuous (fun t : unitInterval.Elem => f (t : ℝ)) := by
    exact (continuousOn_iff_continuous_restrict).mp hf
  refine ⟨⟨fun t => f (t : ℝ), hc⟩, ?_⟩
  intro t
  rfl
