-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_source_product_rectangle_mass_of_cutoffs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:46:58.479912+00:00
-- url     : https://prove2.me/submissions/bc3ecdc7-a502-4080-97f0-e9190e8abe39

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_source_levy_measure_sfinite_of_cutoffs
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_source_compensator_rectangle_mass_of_sfinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original Lévy intensity product compensator has the exact source
rectangle rate using physical off-zero cutoff finiteness alone. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hZero : X.ν ({0} : Set ℝ) = 0)
    (hAway : ∀ n : ℕ,
      X.ν {z : ℝ | 1 / ((n : ℝ) + 1) ≤ |z|} < ⊤)
    (timeMeasure : Measure ℝ≥0) (s t : ℝ≥0) (B : Set ℝ)
    (hTimeVolume : timeMeasure (Ioc s t) =
      ((t - s : ℝ≥0) : ℝ≥0∞)) :
    (timeMeasure.prod X.ν) (Ioc s t ×ˢ B) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  have hSourceSFinite : SFinite X.ν :=
    avram_p4_b_smalljump_original_source_levy_measure_sfinite_of_cutoffs
      X hZero hAway
  exact avram_p4_b_smalljump_original_source_compensator_rectangle_mass_of_sfinite
    X timeMeasure s t B hSourceSFinite hTimeVolume
