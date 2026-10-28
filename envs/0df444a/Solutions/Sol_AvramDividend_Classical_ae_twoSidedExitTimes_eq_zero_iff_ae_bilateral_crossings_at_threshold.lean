-- Prove2me | solution 1 for AvramDividend.Classical.ae_twoSidedExitTimes_eq_zero_iff_ae_bilateral_crossings_at_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:11:27.383311+00:00
-- url     : https://prove2.me/submissions/74007bfa-8f2c-4012-b732-8f012b18ab25

import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_eq_zero_iff_crossings_at_threshold
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_eq_zero_iff_crossings_at_threshold
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-! Almost-sure bilateral regularity follows pointwise from the two accepted exit-time equivalences. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) :
    (∀ᵐ ω ∂P,
      twoSidedExitDownTime X b ω = 0 ∧ twoSidedExitUpTime X b ω = 0) ↔
      (∀ᵐ ω ∂P,
        (∀ ε : ℝ≥0, 0 < ε →
          ∃ t : ℝ≥0, t < ε ∧ X.X t ω < b) ∧
        (∀ ε : ℝ≥0, 0 < ε →
          ∃ t : ℝ≥0, t < ε ∧ b < X.X t ω)) := by
  constructor
  · intro h
    exact h.mono (fun ω hω =>
      ⟨(twoSidedExitDownTime_eq_zero_iff_crossings_at_threshold X b ω).mp hω.1,
       (twoSidedExitUpTime_eq_zero_iff_crossings_at_threshold X b ω).mp hω.2⟩)
  · intro h
    exact h.mono (fun ω hω =>
      ⟨(twoSidedExitDownTime_eq_zero_iff_crossings_at_threshold X b ω).mpr hω.1,
       (twoSidedExitUpTime_eq_zero_iff_crossings_at_threshold X b ω).mpr hω.2⟩)
