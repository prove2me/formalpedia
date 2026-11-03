-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_shifted_future_increment_stationary_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:43:30.875029+00:00
-- url     : https://prove2.me/submissions/0a17ce70-c9a7-4de0-901c-7dc44c5b6aec

import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- A future increment on the original Ω has the same law as the zero-origin increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0) :
    IdentDistrib
      (fun ω => X.X (s + t) ω - X.X s ω)
      (X.X t) P P := by
  have hs : s ≤ s + t := by simp
  simpa only [add_tsub_cancel_left] using
    (X.stationaryIncrements s (s + t) hs)
