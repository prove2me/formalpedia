-- Prove2me | solution 1 for AvramDividend.Classical.ae_twoSidedExitDownTime_eq_zero_iff_ae_near_threshold_crossings
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:56:11.250817+00:00
-- url     : https://prove2.me/submissions/b612bc75-8c5e-49f7-a9ac-f475312231dc

import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_eq_zero_iff_crossings_at_threshold
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
    (∀ᵐ ω ∂P, twoSidedExitDownTime X b ω = 0) ↔
      (∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
        ∃ t : ℝ≥0, t < ε ∧ X.X t ω < b) := by
  constructor
  · intro h
    exact h.mono (fun ω hω => (twoSidedExitDownTime_eq_zero_iff_crossings_at_threshold X b ω).mp hω)
  · intro h
    exact h.mono (fun ω hω => (twoSidedExitDownTime_eq_zero_iff_crossings_at_threshold X b ω).mpr hω)
