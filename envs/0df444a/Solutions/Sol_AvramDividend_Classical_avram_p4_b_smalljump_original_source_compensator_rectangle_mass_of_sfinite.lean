-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_source_compensator_rectangle_mass_of_sfinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:30:51.194265+00:00
-- url     : https://prove2.me/submissions/c31338b0-2bf0-4639-a84e-ffe1fb85855e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Under an explicit sigma-finiteness certificate for the original source
Levy measure, the physical-time/product compensator rectangle mass is the
source interval-volume rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (timeMeasure : Measure ℝ≥0) (s t : ℝ≥0) (B : Set ℝ)
    (hNuSFinite : SFinite X.ν)
    (hTimeVolume : timeMeasure (Ioc s t) =
      ((t - s : ℝ≥0) : ℝ≥0∞)) :
    (timeMeasure.prod X.ν) (Ioc s t ×ˢ B) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  letI : SFinite X.ν := hNuSFinite
  rw [Measure.prod_prod, hTimeVolume]
