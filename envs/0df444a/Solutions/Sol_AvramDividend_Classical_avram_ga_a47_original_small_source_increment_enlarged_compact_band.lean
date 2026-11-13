-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a47_original_small_source_increment_enlarged_compact_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:57:10.532859+00:00
-- url     : https://prove2.me/submissions/98fe733b-d7cd-400f-bc19-f12b4870dc75

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

-- Small genuine original source displacement preserves a positive enlarged spatial Taylor band.
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (s t : ℝ≥0)
    (a b δ : ℝ) (ha : 0 < a) (hδ : 0 ≤ δ)
    (hδa : δ ≤ a / 2)
    (hBand : a ≤ x + X.X s ω - rightLimit D s ω ∧
      x + X.X s ω - rightLimit D s ω ≤ b)
    (hInc : |X.X t ω - X.X s ω| ≤ δ) :
    a / 2 ≤ x + X.X t ω - rightLimit D s ω ∧
      x + X.X t ω - rightLimit D s ω ≤ b + a / 2 := by
  obtain ⟨hl, hu⟩ := abs_le.mp hInc
  constructor
  · linarith [hBand.1]
  · linarith [hBand.2]
