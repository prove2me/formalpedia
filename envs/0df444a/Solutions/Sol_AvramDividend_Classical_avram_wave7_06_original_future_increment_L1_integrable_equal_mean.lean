-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_future_increment_L1_integrable_equal_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:51:53.5076+00:00
-- url     : https://prove2.me/submissions/e81089a0-9d00-4525-ad63-3100ce02325b

import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Source future increments transport integrability and expectation from time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (hInt : Integrable (X.X t) P) :
    Integrable (fun ω => X.X (s + t) ω - X.X s ω) P ∧
    (∫ ω, (X.X (s + t) ω - X.X s ω) ∂P) =
      ∫ ω, X.X t ω ∂P := by
  have hs : s ≤ s + t := by simp
  have hLaw :
      IdentDistrib
        (fun ω => X.X (s + t) ω - X.X s ω)
        (X.X t) P P := by
    simpa only [add_tsub_cancel_left] using
      (X.stationaryIncrements s (s + t) hs)
  exact ⟨hLaw.integrable_iff.mpr hInt, hLaw.integral_eq⟩
