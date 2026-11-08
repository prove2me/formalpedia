-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_original_filtration_bracket_adapted_sfinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:49:29.015266+00:00
-- url     : https://prove2.me/submissions/7636dca4-1196-466b-b239-99f1ed1aaab1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The stopped Gaussian quadratic-variation integral is measurable in the
original filtration when the predictable-band trace is product measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω × ℝ≥0 → ℝ) (μtime : Measure ℝ≥0) [SFinite μtime]
    (hBand : ∀ b : ℝ≥0,
      Measurable[@Prod.instMeasurableSpace Ω ℝ≥0 (𝓕 b) inferInstance]
        (fun z : Ω × ℝ≥0 =>
          (Ioc 0 b).indicator (fun t => (H (z.1, t)) ^ 2) z.2)) :
    Adapted 𝓕 (fun b ω => ∫ t in Ioc (0 : ℝ≥0) b, (H (ω, t)) ^ 2 ∂μtime) := by
  intro b
  have hm : Measurable[𝓕 b]
      (fun ω => ∫ t, (Ioc (0 : ℝ≥0) b).indicator
        (fun s => (H (ω, s)) ^ 2) t ∂μtime) := by
    letI : MeasurableSpace Ω := 𝓕 b
    exact ((hBand b).stronglyMeasurable.integral_prod_right').measurable
  convert hm using 1
  funext ω
  exact (integral_indicator measurableSet_Ioc).symm
