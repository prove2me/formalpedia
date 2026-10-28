-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_preUpcrossingRuin_iff_lowerClockBefore
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:13:26.15349+00:00
-- url     : https://prove2.me/submissions/1f828d93-5b57-4e1a-8af9-c38c24450420

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_ruinBeforeFirstUpcrossing_iff_rawDowncrossing
import Theorems.Thm_AvramDividend_Classical_lowerCrossingClock_lt_horizon_iff_exists_witness
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Controlled ruin strictly before a finite first upcrossing
    is exactly the lower first-passage clock lying before that time. -/
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
  rw [barrierStrategy_ruinBeforeFirstUpcrossing_iff_rawDowncrossing
    X x a ω u hu]
  exact (lowerCrossingClock_lt_horizon_iff_exists_witness
    X (-x) ω u).symm
