-- Prove2me | solution 1 for AvramDividend.Classical.levy_shifted_increment_law_at_fixed_offset
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T08:13:54.759339+00:00
-- url     : https://prove2.me/submissions/c8bbc761-a815-4087-932b-9f2d0cd3fb72

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0) :
    Measure.map (fun ω : Ω => X.X (s + t) ω - X.X s ω) P =
      Measure.map (fun ω : Ω => X.X t ω) P := by
  have h := (X.stationaryIncrements s (s + t) le_self_add).map_eq
  rwa [add_tsub_cancel_left] at h
