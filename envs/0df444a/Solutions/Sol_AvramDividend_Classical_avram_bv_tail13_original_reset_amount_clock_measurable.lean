-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_tail13_original_reset_amount_clock_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:30:33.037177+00:00
-- url     : https://prove2.me/submissions/15719774-0ddb-4cb5-b7b8-187a22c71282

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The nonnegative original-process surplus measured at a fixed payment
clock is measurable for the actual Lévy filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (s : ℝ≥0) :
    Measurable[𝓕 s] (fun ω => max (x + X.X s ω) (0 : ℝ)) := by
  exact (measurable_const.add (X.adapted s)).max measurable_const
