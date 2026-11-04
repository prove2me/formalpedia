-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_raw_large_cutoff_unit_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:01:24.677561+00:00
-- url     : https://prove2.me/submissions/a2e8289e-1057-4ba4-90b1-f3db83e734b1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_large_negative_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_finite_band_raw_integrable

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
    (∫ z in Iio (-ε), w (y + z) - w y ∂X.ν) =
      (∫ z in Iic (-1 : ℝ), w (y + z) - w y ∂X.ν) +
      (∫ z in Ioo (-1 : ℝ) (-ε), w (y + z) - w y ∂X.ν) := by
  have hbig : IntegrableOn (fun z : ℝ => w (y + z) - w y)
      (Iic (-1 : ℝ)) X.ν :=
    generatorIntegrand_large_negative_integrable X w y hgen
  have hmid : IntegrableOn (fun z : ℝ => w (y + z) - w y)
      (Ioo (-1 : ℝ) (-ε)) X.ν :=
    avram_p4_c_generator_finite_band_raw_integrable X w y ε hε hgen
  have hε1' : (-1 : ℝ) < -ε := by linarith
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
