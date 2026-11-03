-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_shifted_future_increment_square_identDistrib
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:45:19.060438+00:00
-- url     : https://prove2.me/submissions/3644b6b7-7dbc-4e8c-b31d-a995de7639d7

import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Second-power future increment statistics have the original zero-origin source law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0) :
    IdentDistrib
      (fun ω => (X.X (s + t) ω - X.X s ω) ^ (2 : ℕ))
      (fun ω => (X.X t ω) ^ (2 : ℕ)) P P := by
  have hs : s ≤ s + t := by simp
  have hLaw :
      IdentDistrib
        (fun ω => X.X (s + t) ω - X.X s ω)
        (X.X t) P P := by
    simpa only [add_tsub_cancel_left] using
      (X.stationaryIncrements s (s + t) hs)
  have hSquare : Measurable (fun x : ℝ => x ^ (2 : ℕ)) := by
    fun_prop
  simpa only [Function.comp_def] using (hLaw.comp hSquare)
