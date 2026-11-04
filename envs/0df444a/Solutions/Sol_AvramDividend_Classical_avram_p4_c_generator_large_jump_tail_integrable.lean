-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_large_jump_tail_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:05:41.608922+00:00
-- url     : https://prove2.me/submissions/4619c72e-1339-4093-98b6-0d40b3c5e0b2

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (y : ℝ)
    (hgen : X.GeneratorIntegrable w y) :
    IntegrableOn (fun z : ℝ => w (y + z) - w y)
      (Iio (-1 : ℝ)) X.ν := by
  change IntegrableOn (SpectrallyNegativeLevy.generatorIntegrand w y) (Iio 0) X.ν at hgen
  have hsub : Iio (-1 : ℝ) ⊆ Iio (0 : ℝ) := by
    intro z hz
    change z < (-1 : ℝ) at hz
    change z < (0 : ℝ)
    exact lt_trans hz (by norm_num)
  have hlarge : IntegrableOn (SpectrallyNegativeLevy.generatorIntegrand w y)
      (Iio (-1 : ℝ)) X.ν := hgen.mono_set hsub
  have hsame : Set.EqOn (SpectrallyNegativeLevy.generatorIntegrand w y)
      (fun z : ℝ => w (y + z) - w y) (Iio (-1 : ℝ)) := by
    intro z hz
    change z < (-1 : ℝ) at hz
    have hnot : z ∉ Ioo (-1 : ℝ) 1 := by
      intro hm
      exact (not_lt_of_ge (le_of_lt hz)) hm.1
    simp [SpectrallyNegativeLevy.generatorIntegrand, Set.indicator_of_notMem hnot]
  exact hlarge.congr_fun hsame measurableSet_Iio
