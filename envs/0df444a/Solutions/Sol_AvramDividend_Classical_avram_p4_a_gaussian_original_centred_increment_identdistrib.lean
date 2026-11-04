-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_centred_increment_identdistrib
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:08:54.278656+00:00
-- url     : https://prove2.me/submissions/69157850-6dc7-4e91-912a-2c8a559df797

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

/-- Drift centring preserves the original Levy stationary-increment law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) :
    IdentDistrib
      (fun ω => (Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)
      (fun ω => Y.X (t - s) ω - ((t - s : ℝ≥0) : ℝ) * Y.c)
      P P := by
  have hAffine : Measurable (fun z : ℝ =>
      z - ((t - s : ℝ≥0) : ℝ) * Y.c) := by
    fun_prop
  exact (Y.stationaryIncrements s t hst).comp hAffine
