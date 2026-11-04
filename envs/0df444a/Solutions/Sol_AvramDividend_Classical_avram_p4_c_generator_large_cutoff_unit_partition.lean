-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_large_cutoff_unit_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:46:14.809523+00:00
-- url     : https://prove2.me/submissions/6bb968d1-532e-4d8e-a791-146709a16664

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
    (hε : 0 < ε) (hε1 : ε < 1) (hgen : X.GeneratorIntegrable w y) :
    (∫ z in Iio (-ε), SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) =
      (∫ z in Iic (-1 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) +
      (∫ z in Ioo (-1 : ℝ) (-ε),
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) := by
  have hneg : -ε < (0 : ℝ) := by linarith
  have hε1' : (-1 : ℝ) < -ε := by linarith
  have hbig : IntegrableOn (SpectrallyNegativeLevy.generatorIntegrand w y)
      (Iic (-1 : ℝ)) X.ν := hgen.mono_set (by
    intro z hz
    exact lt_trans (lt_of_le_of_lt hz hε1') hneg)
  have hmid : IntegrableOn (SpectrallyNegativeLevy.generatorIntegrand w y)
      (Ioo (-1 : ℝ) (-ε)) X.ν := hgen.mono_set (by
    intro z hz
    exact lt_trans hz.2 hneg)
  have hd : Disjoint (Iic (-1 : ℝ)) (Ioo (-1 : ℝ) (-ε)) := by
    refine disjoint_left.mpr ?_
    intro z hzbig hzmid
    exact (not_lt_of_ge hzbig) hzmid.1
  have hU : (Iic (-1 : ℝ) ∪ Ioo (-1 : ℝ) (-ε)) = Iio (-ε) := by
    ext z
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioo, Set.mem_Iio]
    constructor
    · rintro (h | ⟨_, h⟩)
      · exact lt_of_le_of_lt h hε1'
      · exact h
    · intro hz
      by_cases h : z ≤ -1
      · exact Or.inl h
      · exact Or.inr ⟨lt_of_not_ge h, hz⟩
  rw [← hU]
  exact MeasureTheory.setIntegral_union hd measurableSet_Ioo hbig hmid
