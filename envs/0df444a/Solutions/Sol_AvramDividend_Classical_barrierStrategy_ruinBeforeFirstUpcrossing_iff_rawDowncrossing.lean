-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_ruinBeforeFirstUpcrossing_iff_rawDowncrossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:02:29.041989+00:00
-- url     : https://prove2.me/submissions/9327af71-114c-4378-8cbc-a8ad51a919de

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_preUpcrossing_ruin_iff_rawDowncrossing
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The existence of ruin before first upper entry is exactly the existence
    of a strict downward crossing of the raw path before that entry. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    (∃ t : ℝ≥0, t < u ∧
       riskProcess X x (barrierStrategy X x a) t ω < 0) ↔
      (∃ t : ℝ≥0, t < u ∧ X.X t ω < -x) := by
  constructor
  · rintro ⟨t, ht, hneg⟩
    exact ⟨t, ht,
      (barrierStrategy_preUpcrossing_ruin_iff_rawDowncrossing
        X x a ω u hu t ht).mp hneg⟩
  · rintro ⟨t, ht, hneg⟩
    exact ⟨t, ht,
      (barrierStrategy_preUpcrossing_ruin_iff_rawDowncrossing
        X x a ω u hu t ht).mpr hneg⟩
