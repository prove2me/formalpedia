-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb24_original_everywhere_zero_reserve_forces_exact_initial_capital_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:41:34.780246+00:00
-- url     : https://prove2.me/submissions/ee772ab6-8008-4dd7-900a-f466c19bc2da

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
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S : ℝ≥0)
    (hZero : ∀ t : ℝ≥0, t ≤ S →
      riskProcess X x D t ω = 0) :
    x = 0  := by
  have hD0 : D 0 ω = 0 := hD.1.1.1 ω
  have hR0 := hZero 0 zero_le
  change x + X.X 0 ω - D 0 ω = 0 at hR0
  simpa [X.X_zero ω, hD0] using hR0
