-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_total_mass_of_zero_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:36:28.849482+00:00
-- url     : https://prove2.me/submissions/6b9e7505-2b71-4f68-9273-3752babdcede

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Zeroth nonnegative monomial moment is the mass of the whole space. -/
theorem solution
    (μ : Measure ℝ)
    (hfinite : (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ 0 ∂μ) ≠ ⊤) :
    μ Set.univ < ⊤ := by
  have hmass : μ Set.univ ≠ ⊤ := by
    simpa only [pow_zero, lintegral_one] using hfinite
  exact lt_top_iff_ne_top.mpr hmass
