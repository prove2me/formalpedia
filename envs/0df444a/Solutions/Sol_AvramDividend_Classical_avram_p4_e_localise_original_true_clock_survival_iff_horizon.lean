-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_true_clock_survival_iff_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:32:55.353577+00:00
-- url     : https://prove2.me/submissions/335430b4-2c3f-45fc-b74f-52840e6ff9cf

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Exact source stopped survival is equivalent to the integer horizon before ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (ω : Ω) :
    (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) <
      ruinTime X x D ω ↔
    (n : ℝ≥0∞) < ruinTime X x D ω := by
  have hClock := avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n
  rw [hClock.1 ω]
  simp [min_lt_iff]
