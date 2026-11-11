-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_bv_standing_from_diffuse_positive_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T15:17:24.100195+00:00
-- url     : https://prove2.me/submissions/b47313f9-d0a2-4796-a6e4-accc90eddfc9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Positive drift, nonzero diffuse negative jumps and a finite first
moment imply the original Standing hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hpos : 0 < X.drift)
    (hne : X.ν ≠ 0)
    (hint : Integrable (X.X 1) P)
    (hac : X.ν ≪ volume) :
    X.Standing := by
  refine ⟨?_, hint, ?_⟩
  · intro hmono
    rcases hmono.2 with hle | hzero
    · exact (not_le_of_gt hpos) hle
    · exact hne hzero
  · right
    right
    exact hac
