-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f12_original_positive_near_zero_germ_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:36:08.027912+00:00
-- url     : https://prove2.me/submissions/c69b363f-f84e-4497-93e8-5a15dbf98e70

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_DurrettProbability_Brownian
import Theorems.Thm_AvramDividend_Classical_avram_p4_f14_original_near_zero_rational_path_equiv
import Theorems.Thm_AvramDividend_Classical_avram_p4_f14_original_near_zero_rational_germ_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical DurrettProbability
open scoped NNReal ENNReal
noncomputable section

/-- Reduce the uncountable positive-near-zero event to two rational-time facts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    MeasurableSet[germSigma X.X] {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ 0 < X.X s ω} := by
  rw [avram_p4_f14_original_near_zero_rational_path_equiv X]
  exact avram_p4_f14_original_near_zero_rational_germ_measurable X
