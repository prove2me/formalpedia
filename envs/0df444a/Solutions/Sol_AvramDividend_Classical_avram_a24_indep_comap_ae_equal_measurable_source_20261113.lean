-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_indep_comap_ae_equal_measurable_source_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:45:49.297659+00:00
-- url     : https://prove2.me/submissions/bc1b0d68-f9a5-4507-a30f-a42ab981963a

import Mathlib.Probability.Independence.Basic
import Theorems.Thm_AvramDividend_Classical_avram_a24_indep_comap_ae_equal_measurable_source_v2_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (A : MeasurableSpace Ω) (hA : A ≤ mΩ)
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hEq : f =ᵐ[P] g)
    (hInd : Indep (MeasurableSpace.comap f inferInstance) A P) :
    Indep (MeasurableSpace.comap g inferInstance) A P  := by
  have hfm : @Measurable Ω ℝ mΩ Real.measurableSpace f :=
    @Measurable.mono Ω ℝ A mΩ Real.measurableSpace
      Real.measurableSpace f hf hA le_rfl
  have hgm : @Measurable Ω ℝ mΩ Real.measurableSpace g :=
    @Measurable.mono Ω ℝ A mΩ Real.measurableSpace
      Real.measurableSpace g hg hA le_rfl
  letI : MeasurableSpace Ω := mΩ
  exact (@avram_a24_indep_comap_ae_equal_measurable_source_v2_20261114
    Ω mΩ P inferInstance A hA f g hfm hgm hEq hInd)
