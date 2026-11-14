-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb24_original_zero_reserve_nojump_source_dividend_exact_physical_linear_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:41:41.095815+00:00
-- url     : https://prove2.me/submissions/29f26f09-d533-45ec-b6bd-4d0f08f3a231

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
      riskProcess X x D t ω = 0)
    (hSource : ∀ t : ℝ≥0, t ≤ S →
      X.X t ω = (t : ℝ) * X.drift) :
    ∀ t : ℝ≥0, t ≤ S → D t ω = (t : ℝ) * X.drift  := by
  have hD0 : D 0 ω = 0 := hD.1.1.1 ω
  have hR0 := hZero 0 zero_le
  change x + X.X 0 ω - D 0 ω = 0 at hR0
  have hx : x = 0 := by
    simpa [X.X_zero ω, hD0] using hR0
  intro t ht
  have h := hZero t ht
  change x + X.X t ω - D t ω = 0 at h
  rw [hx, hSource t ht] at h
  linarith
