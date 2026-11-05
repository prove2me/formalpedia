-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_interior_cap_generator_hjb
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:07:45.308038+00:00
-- url     : https://prove2.me/submissions/3ca0c9f4-5432-4af5-9ccb-c3b467dc6be8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_source_generator_eq_interior
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_source_generatorIntegrable_iff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original-generator and discounted-HJB admissibility pass unchanged to
the slope-one cap extension at every strict interior reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (c y q : ℝ) (hyc : y < c)
    (hw : X.GeneratorIntegrable w y ∧
      X.generator w y - q * w y ≤ 0) :
    X.GeneratorIntegrable
        (fun z => if z ≤ c then w z else w c + (z - c)) y ∧
      X.generator
          (fun z => if z ≤ c then w z else w c + (z - c)) y -
        q * (if y ≤ c then w y else w c + (y - c)) ≤ 0 := by
  constructor
  · exact
      (avram_wave4_04_cap_linear_extension_source_generatorIntegrable_iff
        X w c y hyc).2 hw.1
  · rw [avram_wave4_04_cap_linear_extension_source_generator_eq_interior
        X w c y hyc, if_pos (le_of_lt hyc)]
    exact hw.2
