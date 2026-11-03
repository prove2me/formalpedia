-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_20_original_negative_ruin_overshoot_postpayment_terminal_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:20:53.517882+00:00
-- url     : https://prove2.me/submissions/aaf133bd-e779-45e6-af92-1cda6df98eb3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Strictly negative actual ruin overshoot has zero postpayment continuation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0)
    (hOvershoot : riskProcess X x D t ω < 0) :
    max 0 (Real.exp (-(q * (t : ℝ))) *
      w (x + X.X t ω - rightLimit D t ω)) = 0 := by
  have hmon : D t ω ≤ rightLimit D t ω :=
    dividendStrategy_le_rightLimit D hD ω t
  have hneg : x + X.X t ω - rightLimit D t ω < 0 := by
    change x + X.X t ω - D t ω < 0 at hOvershoot
    linarith
  simp [hw_neg _ hneg]
