-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_unit_finite_measure_family_compact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:17:34.9299+00:00
-- url     : https://prove2.me/submissions/eb2d9155-28c7-4c2c-b5d3-34f92df4af3d

import Mathlib.MeasureTheory.Measure.Prokhorov

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal

/-- The mass-bounded finite measures carried by the closed unit interval
form a compact family for weak convergence. -/
theorem solution (C : ℝ≥0) :
    IsCompact {μ : FiniteMeasure ℝ |
      μ.mass ≤ C ∧ μ (Set.Icc (0 : ℝ) 1)ᶜ = 0} := by
  exact isCompact_setOfPred_finiteMeasure_le_of_isCompact C isCompact_Icc
