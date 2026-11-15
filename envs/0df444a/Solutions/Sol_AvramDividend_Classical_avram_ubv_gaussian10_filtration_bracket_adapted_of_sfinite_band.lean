-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_filtration_bracket_adapted_of_sfinite_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:53:39.514961+00:00
-- url     : https://prove2.me/submissions/4d71ccff-9d57-4658-b9de-27f9926528b9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
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
  letI : MeasurableSpace Ω := 𝓕 b
  change Measurable (fun ω : Ω =>
    ∫ t in Ioc (0 : ℝ≥0) b, (H (ω, t)) ^ 2 ∂μtime)
  have hm : Measurable (fun z : Ω × ℝ≥0 =>
      (Ioc 0 b).indicator (fun t => (H (z.1, t)) ^ 2) z.2) :=
    hBand b
  have hi : Measurable (fun ω : Ω =>
      ∫ t, (Ioc 0 b).indicator (fun u => (H (ω, u)) ^ 2) t ∂μtime) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  simpa only [integral_indicator (measurableSet_Ioc)] using hi
