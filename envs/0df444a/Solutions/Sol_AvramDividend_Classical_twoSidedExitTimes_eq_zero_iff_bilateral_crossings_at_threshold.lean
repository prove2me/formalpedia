-- Prove2me | solution 1 for AvramDividend.Classical.twoSidedExitTimes_eq_zero_iff_bilateral_crossings_at_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:11:23.363966+00:00
-- url     : https://prove2.me/submissions/85f69d87-3764-4e19-9e4c-a8883bd39e0e

import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_eq_zero_iff_crossings_at_threshold
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_eq_zero_iff_crossings_at_threshold
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-! Bilateral regularity at a deterministic threshold is equivalent to two strict near-time-zero crossings. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (ω : Ω) :
    (twoSidedExitDownTime X b ω = 0 ∧ twoSidedExitUpTime X b ω = 0) ↔
      ((∀ ε : ℝ≥0, 0 < ε →
          ∃ t : ℝ≥0, t < ε ∧ X.X t ω < b) ∧
       (∀ ε : ℝ≥0, 0 < ε →
          ∃ t : ℝ≥0, t < ε ∧ b < X.X t ω)) := by
  constructor
  · rintro ⟨hd, hu⟩
    exact ⟨(twoSidedExitDownTime_eq_zero_iff_crossings_at_threshold X b ω).mp hd,
      (twoSidedExitUpTime_eq_zero_iff_crossings_at_threshold X b ω).mp hu⟩
  · rintro ⟨hd, hu⟩
    exact ⟨(twoSidedExitDownTime_eq_zero_iff_crossings_at_threshold X b ω).mpr hd,
      (twoSidedExitUpTime_eq_zero_iff_crossings_at_threshold X b ω).mpr hu⟩
