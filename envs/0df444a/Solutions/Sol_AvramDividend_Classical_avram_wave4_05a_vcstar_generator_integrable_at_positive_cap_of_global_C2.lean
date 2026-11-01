-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05a_vcstar_generator_integrable_at_positive_cap_of_global_C2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:18:50.131713+00:00
-- url     : https://prove2.me/submissions/7dc37792-d6ff-48d8-a23b-18f8bd889c42

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generatorIntegrable_of_min_sq_bound
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_positive_real_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_zero_of_neg
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05a_generator_integrand_global_monotone_C2_quadratic_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Complete local C² source compensated-generator domain at the positive cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (ha : 0 < (cstar W).toReal)
    (hC2 : ContDiffOn ℝ 2 (vcstar W) (Ioi (0 : ℝ))) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal := by
  let a : ℝ := (cstar W).toReal
  change X.GeneratorIntegrable (vcstar W) a
  have hmono : Monotone (vcstar W) :=
    vcstar_monotone_of_positive_real_cstar X q W hW ha
  have hzero : ∀ z : ℝ, z < 0 → vcstar W z = 0 := by
    intro z hz
    exact vcstar_eq_zero_of_neg W z hz
  have hnonneg : ∀ z : ℝ, 0 ≤ vcstar W z := by
    intro z
    by_cases hz : z < 0
    · rw [hzero z hz]
    · have hnegone : vcstar W (-1) = 0 :=
        hzero (-1) (by norm_num)
      have hm : (-1 : ℝ) ≤ z := by linarith
      simpa [hnegone] using hmono hm
  have hx : a ∈ Ioo 0 (a + 1) := ⟨ha, by linarith⟩
  have hC2local : ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (a + 1)) :=
    hC2.mono (by intro z hz; exact hz.1)
  obtain ⟨C, hC, hbound⟩ :=
    AvramDividend.Classical.avram_wave4_05a_generator_integrand_global_monotone_C2_quadratic_bound
      X (vcstar W) hzero hnonneg hmono (a + 1) a hx hC2local
  apply generatorIntegrable_of_min_sq_bound X (vcstar W) a C hC
  · have hshift : Measurable (fun y : ℝ => vcstar W (a + y)) :=
      hmono.measurable.comp (measurable_const.add measurable_id)
    have hind :
        Measurable
          (fun y : ℝ =>
            (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y) :=
      measurable_const.indicator measurableSet_Ioo
    have hmeas :
        Measurable (SpectrallyNegativeLevy.generatorIntegrand (vcstar W) a) := by
      unfold SpectrallyNegativeLevy.generatorIntegrand
      exact (hshift.sub measurable_const).sub
        ((measurable_const.mul measurable_id).mul hind)
    exact hmeas.aestronglyMeasurable
  · filter_upwards [MeasureTheory.self_mem_ae_restrict
        (μ := X.ν) measurableSet_Iio] with y hy
    exact hbound y hy
