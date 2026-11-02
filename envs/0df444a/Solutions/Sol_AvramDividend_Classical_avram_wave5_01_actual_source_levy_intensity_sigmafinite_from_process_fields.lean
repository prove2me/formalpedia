-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_levy_intensity_sigmafinite_from_process_fields
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:07:49.181439+00:00
-- url     : https://prove2.me/submissions/e060503c-8a65-49eb-a4f5-d1aa51aefe4b

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_negative_levy_measure_sigmaFinite

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The Levy intensity of the actual source process is sigma-finite from
its pinned source Levy-integrability and negative-support fields alone. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    SigmaFinite X.ν := by
  have hle :
      (∫⁻ y in Iio (0 : ℝ),
        ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) ≤
      (∫⁻ y,
        ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) := by
    simpa using (lintegral_mono_set
      (Set.subset_univ (Iio (0 : ℝ))) :
      (∫⁻ y in Iio (0 : ℝ),
        ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) ≤
      (∫⁻ y in Set.univ,
        ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν))
  exact avram_wave4_04b_negative_levy_measure_sigmaFinite
    X.ν X.ν_Ici (lt_of_le_of_lt hle X.ν_integrable)
