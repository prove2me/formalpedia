-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_positive_ae_of_nonpositive_mass_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:08:03.584119+00:00
-- url     : https://prove2.me/submissions/c680bd36-5b29-4e9a-81cb-d964dbaf5a15

import Mathlib.MeasureTheory.Function.L1Space.Integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Excluding all mass from the nonpositive halfline gives a.e. positivity. -/
theorem solution
    (μ : Measure ℝ) (hzero : μ (Set.Iic (0 : ℝ)) = 0) :
    ∀ᵐ z ∂μ, 0 < z := by
  have hs : {z : ℝ | ¬ 0 < z} = Set.Iic (0 : ℝ) := by
    ext z
    simp only [Set.mem_setOf_eq, not_lt, Set.mem_Iic]
  exact (ae_iff).2 (by simpa only [hs] using hzero)
