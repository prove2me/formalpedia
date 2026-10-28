-- Prove2me | solution 2 for AvramDividend.Classical.barrierStrategy_preUpcrossingRuin_iff_lowerClockBefore
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:14:17.348257+00:00
-- url     : https://prove2.me/submissions/9f95e4c6-d7d3-4c63-bfec-3f74dcf9d241

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_ruinBeforeFirstUpcrossing_iff_rawDowncrossing
import Theorems.Thm_AvramDividend_Classical_lowerCrossingClock_lt_horizon_iff_exists_witness

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    (∃ t : ℝ≥0, t < u ∧
       riskProcess X x (barrierStrategy X x a) t ω < 0) ↔
    (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) <
      (u : ℝ≥0∞) := by
  rw [AvramDividend.Classical.barrierStrategy_ruinBeforeFirstUpcrossing_iff_rawDowncrossing X x a ω u hu,
    AvramDividend.Classical.lowerCrossingClock_lt_horizon_iff_exists_witness]
