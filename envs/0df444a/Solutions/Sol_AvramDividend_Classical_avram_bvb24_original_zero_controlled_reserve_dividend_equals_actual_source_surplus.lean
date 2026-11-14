-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb24_original_zero_controlled_reserve_dividend_equals_actual_source_surplus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:38:15.567203+00:00
-- url     : https://prove2.me/submissions/bf8d5463-cedc-4e7c-b125-90648fc96f05

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (S : ℝ≥0)
    (hZero : ∀ t : ℝ≥0, t ≤ S →
      riskProcess X x D t ω = 0) :
    ∀ t : ℝ≥0, t ≤ S → D t ω = x + X.X t ω  := by
  intro t ht
  have h := hZero t ht
  change x + X.X t ω - D t ω = 0 at h
  linarith
