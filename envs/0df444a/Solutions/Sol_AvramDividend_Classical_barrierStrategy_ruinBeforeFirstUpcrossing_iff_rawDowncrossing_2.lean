-- Prove2me | solution 2 for AvramDividend.Classical.barrierStrategy_ruinBeforeFirstUpcrossing_iff_rawDowncrossing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:04:03.117876+00:00
-- url     : https://prove2.me/submissions/d5dcdaf3-172c-4d8c-8a56-e09355219ae4

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_preUpcrossing_ruin_iff_rawDowncrossing

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
      (∃ t : ℝ≥0, t < u ∧ X.X t ω < -x) := by
  have h := AvramDividend.Classical.barrierStrategy_preUpcrossing_ruin_iff_rawDowncrossing X x a ω u hu
  constructor
  · rintro ⟨t, ht, h1⟩; exact ⟨t, ht, (h t ht).1 h1⟩
  · rintro ⟨t, ht, h1⟩; exact ⟨t, ht, (h t ht).2 h1⟩
