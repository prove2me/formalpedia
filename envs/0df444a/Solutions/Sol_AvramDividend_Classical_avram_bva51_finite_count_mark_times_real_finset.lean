-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva51_finite_count_mark_times_real_finset
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:30:27.273652+00:00
-- url     : https://prove2.me/submissions/220b3551-705d-4635-a4d0-7afa27b771d6

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

/-- Finite counting mass permits a finite real-time enumeration of jump times. -/
theorem solution (S : Set ℝ≥0) (hCount : (Measure.count S) < ⊤) :
    ∃ F : Finset ℝ, ∀ t : ℝ≥0, t ∈ S ↔ (t : ℝ) ∈ F := by
  classical
  have hFinite : S.Finite := (Measure.count_apply_lt_top).1 hCount
  refine ⟨hFinite.toFinset.image (fun t : ℝ≥0 => (t : ℝ)), ?_⟩
  intro t
  simp only [Finset.mem_image, Set.Finite.mem_toFinset]
  constructor
  · intro ht
    exact ⟨t, ht, rfl⟩
  · rintro ⟨u, hu, hEq⟩
    have hUt : u = t := NNReal.coe_injective hEq
    exact hUt ▸ hu
