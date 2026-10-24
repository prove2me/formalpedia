-- Prove2me | solution 1 for AvramDividend.Classical.generatorIntegral_negative_jump_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:29:09.422674+00:00
-- url     : https://prove2.me/submissions/7ff64acf-eed9-4bb7-8680-3d87dffa7637

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Split the generator jump integral at the strict truncation boundary. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    (∫ y in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w x y ∂X.ν) =
      (∫ y in Ioo (-1 : ℝ) 0, SpectrallyNegativeLevy.generatorIntegrand w x y ∂X.ν) +
      (∫ y in Iic (-1 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w x y ∂X.ν) := by
  have hSmall : IntegrableOn (SpectrallyNegativeLevy.generatorIntegrand w x)
      (Ioo (-1 : ℝ) 0) X.ν := hGen.mono_set (by
    intro y hy
    exact hy.2)
  have hLarge : IntegrableOn (SpectrallyNegativeLevy.generatorIntegrand w x)
      (Iic (-1 : ℝ)) X.ν := hGen.mono_set (by
    intro y hy
    change y ≤ (-1 : ℝ) at hy
    change y < (0 : ℝ)
    exact lt_of_le_of_lt hy (by norm_num))
  have hd : Disjoint (Ioo (-1 : ℝ) 0) (Iic (-1 : ℝ)) := by
    refine disjoint_left.mpr ?_
    intro y hySmall hyLarge
    exact (not_lt_of_ge hyLarge) hySmall.1
  have hU : (Ioo (-1 : ℝ) 0 ∪ Iic (-1 : ℝ)) = Iio 0 := by
    ext y
    simp only [mem_union, mem_Ioo, mem_Iic, mem_Iio]
    constructor
    · rintro (⟨_, hy⟩ | hy)
      · exact hy
      · exact lt_of_le_of_lt hy (by norm_num)
    · intro hy
      by_cases h : y ≤ (-1 : ℝ)
      · exact Or.inr h
      · exact Or.inl ⟨lt_of_not_ge h, hy⟩
  rw [← hU]
  exact MeasureTheory.setIntegral_union hd measurableSet_Iic hSmall hLarge
