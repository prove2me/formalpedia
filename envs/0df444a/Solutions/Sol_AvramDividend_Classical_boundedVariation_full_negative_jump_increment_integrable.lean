-- Prove2me | solution 1 for AvramDividend.Classical.boundedVariation_full_negative_jump_increment_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:21:54.018602+00:00
-- url     : https://prove2.me/submissions/9fda9519-fad3-4835-956d-7f8a854bee21

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_uncompensated_integrable
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_large_negative_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The full negative-jump value increment is integrable in the BV case. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    IntegrableOn (fun y : ℝ => w (x + y) - w x) (Iio 0) X.ν := by
  have hSmall :=
    boundedVariation_smallJump_uncompensated_integrable X hBV w x hGen
  have hLarge :=
    generatorIntegrand_large_negative_integrable X w x hGen
  have hUnion : (Ioo (-1 : ℝ) 0 ∪ Iic (-1 : ℝ)) = Iio 0 := by
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
  rw [← hUnion]
  exact hSmall.union hLarge
