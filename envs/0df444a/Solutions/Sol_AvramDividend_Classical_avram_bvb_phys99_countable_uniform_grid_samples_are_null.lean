-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys99_countable_uniform_grid_samples_are_null
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:37:00.439197+00:00
-- url     : https://prove2.me/submissions/b503efaa-78ec-4233-a42c-22605cbbb450

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- All points from countably many finite deterministic grids form a
Lebesgue-null measurable set, irrespective of their mesh geometry. -/
theorem solution (u : ℕ → ℕ → ℝ) :
    let G : Set ℝ := Set.range (fun p : ℕ × ℕ => u p.1 p.2)
    MeasurableSet G ∧ (volume : Measure ℝ) G = 0 := by
  dsimp
  have hcount : (Set.range (fun p : ℕ × ℕ => u p.1 p.2)).Countable :=
    Set.countable_range _
  exact ⟨hcount.measurableSet, hcount.measure_zero volume⟩
