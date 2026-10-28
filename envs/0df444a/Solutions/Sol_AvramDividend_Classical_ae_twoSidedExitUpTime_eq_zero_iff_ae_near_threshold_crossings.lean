-- Prove2me | solution 1 for AvramDividend.Classical.ae_twoSidedExitUpTime_eq_zero_iff_ae_near_threshold_crossings
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:56:17.277335+00:00
-- url     : https://prove2.me/submissions/77b1a782-3913-4a44-aa6f-d4bbf81b2508

import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_eq_zero_iff_crossings_at_threshold
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- Lift the pointwise first-passage equivalence to an almost-sure law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) :
    (∀ᵐ ω ∂P, twoSidedExitUpTime X b ω = 0) ↔
      (∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ b < X.X t ω) := by
  constructor
  · intro h
    exact h.mono (fun ω hω => (twoSidedExitUpTime_eq_zero_iff_crossings_at_threshold X b ω).mp hω)
  · intro h
    exact h.mono (fun ω hω => (twoSidedExitUpTime_eq_zero_iff_crossings_at_threshold X b ω).mpr hω)
