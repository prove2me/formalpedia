-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB283_finite_physical_time_mesh_endpoints_null_volume
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:47:00.484676+00:00
-- url     : https://prove2.me/submissions/65773f17-d305-4558-b2d0-d6c53d54e14f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

/-- The finite set of physical mesh endpoints has zero real Lebesgue measure. -/
theorem solution (N : ℕ) (δ : ℝ) :
    volume (Set.range (fun i : Fin N => (i : ℝ) * δ)) = 0 := by
  exact (Set.finite_range (fun i : Fin N => (i : ℝ) * δ)).measure_zero volume
