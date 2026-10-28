-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_ruinClock_lt_upClock_iff_rawLowerClock_lt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:26:17.238586+00:00
-- url     : https://prove2.me/submissions/93c12e4f-406d-4aa9-a2db-1b2c621c433d

import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_preUpcrossingRuin_iff_lowerClockBefore

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
    ruinTime X x (barrierStrategy X x a) ω < (u : ℝ≥0∞) ↔
      (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) <
        (u : ℝ≥0∞) := by
  rw [← AvramDividend.Classical.barrierStrategy_preUpcrossingRuin_iff_lowerClockBefore X x a ω u hu]
  unfold ruinTime
  simp only [iInf_lt_iff, ENNReal.coe_lt_coe]
  constructor
  · rintro ⟨t, ht, h⟩; exact ⟨t, h, ht⟩
  · rintro ⟨t, h, ht⟩; exact ⟨t, ht, h⟩
