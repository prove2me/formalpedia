-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorIntegrand_aestronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T13:53:50.07882+00:00
-- url     : https://prove2.me/submissions/37f067b6-a22b-4e2c-8cbe-e7953a8a03fa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (x : ℝ) :
    AEStronglyMeasurable
      (SpectrallyNegativeLevy.generatorIntegrand W x)
      (X.ν.restrict (Iio 0)) := by
  have hmono : Monotone W := by
    intro u v huv
    by_cases hv : v < 0
    · have hu : u < 0 := lt_of_le_of_lt huv hv
      rw [hW.1 u hu, hW.1 v hv]
    · have hv0 : 0 ≤ v := le_of_not_gt hv
      by_cases hu : u < 0
      · rw [hW.1 u hu]
        exact hW.2.1 v hv0
      · have hu0 : 0 ≤ u := le_of_not_gt hu
        exact hW.2.2.2.1 hu0 hv0 huv
  have hWmeas : Measurable W := hmono.measurable
  have hshift : Measurable (fun y : ℝ => W (x + y)) := by
    exact hWmeas.comp (measurable_const.add measurable_id)
  have hind :
      Measurable
        (fun y : ℝ =>
          (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y) := by
    exact measurable_const.indicator measurableSet_Ioo
  have hgen :
      Measurable (SpectrallyNegativeLevy.generatorIntegrand W x) := by
    unfold SpectrallyNegativeLevy.generatorIntegrand
    exact (hshift.sub measurable_const).sub
      ((measurable_const.mul measurable_id).mul hind)
  exact hgen.aestronglyMeasurable
