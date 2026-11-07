-- Prove2me | solution 1 for AvramDividend.Classical.ae_positive_near_zero_of_unbounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:18:31.280194+00:00
-- url     : https://prove2.me/submissions/479a6a30-fc8a-4495-9964-bbed9fa79d85
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_DurrettProbability_Brownian
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_original_positive_germ_mass_to_ae
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_original_positive_near_zero_germ_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_original_positive_near_zero_positive_mass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical DurrettProbability
open scoped NNReal ENNReal
noncomputable section

/-- Separate path germ measurability and genuine positive small-time excursion mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ 0 < X.X s ω := by
  let A : Set Ω := {ω | ∀ ε : ℝ≥0, 0 < ε →
    ∃ s : ℝ≥0, s < ε ∧ 0 < X.X s ω}
  have hA : MeasurableSet[germSigma X.X] A :=
    avram_p4_f12_original_positive_near_zero_germ_measurable X
  have hPos : 0 < P.real A :=
    avram_p4_f12_original_positive_near_zero_positive_mass X hnbv
  have hAlmost := avram_p4_f12_original_positive_germ_mass_to_ae X A hA hPos
  simpa only [A, Set.mem_setOf_eq] using hAlmost
