-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_negative_mark_integral_cutoff_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:53:58.12984+00:00
-- url     : https://prove2.me/submissions/0429869e-b8c3-41d8-ab2d-3bc17dc1dd7c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (y ε : ℝ)
    (hε : 0 < ε) (hgen : X.GeneratorIntegrable w y) :
    (∫ z in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) =
      (∫ z in Iio (-ε), SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) +
      (∫ z in Ico (-ε) 0, SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) := by
  have hεneg : -ε < (0 : ℝ) := by linarith
  have hlarge : IntegrableOn (SpectrallyNegativeLevy.generatorIntegrand w y)
      (Iio (-ε)) X.ν := hgen.mono_set (by
    intro z hz
    exact lt_trans hz hεneg)
  have hsmall : IntegrableOn (SpectrallyNegativeLevy.generatorIntegrand w y)
      (Ico (-ε) 0) X.ν := hgen.mono_set (by
    intro z hz
    exact hz.2)
  have hd : Disjoint (Iio (-ε)) (Ico (-ε) 0) := by
    refine disjoint_left.mpr ?_
    intro z hzlarge hzsmall
    exact (not_lt_of_ge hzsmall.1) hzlarge
  have hU : (Iio (-ε) ∪ Ico (-ε) 0) = Iio (0 : ℝ) := by
    ext z
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_Ico]
    constructor
    · rintro (hz | ⟨_, hz⟩)
      · exact lt_trans hz hεneg
      · exact hz
    · intro hz
      by_cases h : z < -ε
      · exact Or.inl h
      · exact Or.inr ⟨le_of_not_gt h, hz⟩
  rw [← hU]
  exact MeasureTheory.setIntegral_union hd measurableSet_Ico hlarge hsmall
