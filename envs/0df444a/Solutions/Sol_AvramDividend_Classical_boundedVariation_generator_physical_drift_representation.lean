-- Prove2me | solution 1 for AvramDividend.Classical.boundedVariation_generator_physical_drift_representation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:33:26.513289+00:00
-- url     : https://prove2.me/submissions/e21a869c-da72-4b02-9d8b-7f4dced11067

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_eq_drift_integral
import Theorems.Thm_AvramDividend_Classical_boundedVariation_drift_compensation_identity
import Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable
import Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_generatorIntegral_decomposition
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_large_negative_integral_identity
import Theorems.Thm_AvramDividend_Classical_generatorIntegral_negative_jump_partition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Rewrite the BV Lévy generator with its physical drift and raw jump increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (x : ℝ) (hGen : X.GeneratorIntegrable w x) :
    X.generator w x = X.drift * deriv w x +
      ∫ y in Iio (0 : ℝ), w (x + y) - w x ∂X.ν := by
  have hFull :=
    boundedVariation_full_negative_jump_increment_integrable X hBV w x hGen
  have hS := hFull.mono_set (show Ioo (-1 : ℝ) 0 ⊆ Iio 0 from by
    intro y hy
    exact hy.2)
  have hL := hFull.mono_set (show Iic (-1 : ℝ) ⊆ Iio 0 from by
    intro y hy
    change y ≤ (-1 : ℝ) at hy
    change y < (0 : ℝ)
    exact lt_of_le_of_lt hy (by norm_num))
  have hd : Disjoint (Ioo (-1 : ℝ) 0) (Iic (-1 : ℝ)) := by
    refine disjoint_left.mpr ?_
    intro y hyS hyL
    exact (not_lt_of_ge hyL) hyS.1
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
  have hVal :
      (∫ y in Iio (0 : ℝ), w (x + y) - w x ∂X.ν) =
        (∫ y in Ioo (-1 : ℝ) 0, w (x + y) - w x ∂X.ν) +
        (∫ y in Iic (-1 : ℝ), w (x + y) - w x ∂X.ν) := by
    rw [← hU]
    exact MeasureTheory.setIntegral_union hd measurableSet_Iic hS hL
  have hJ := generatorIntegral_negative_jump_partition X w x hGen
  have hSgen :=
    boundedVariation_smallJump_generatorIntegral_decomposition X hBV w x hGen
  have hLgen := generatorIntegrand_large_negative_integral_identity w x X.ν
  have hDrift := boundedVariation_drift_compensation_identity X hBV w x
  calc
    X.generator w x =
        X.c * deriv w x +
          ∫ y in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w x y ∂X.ν := by
            simpa [SpectrallyNegativeLevy.generatorIntegrand] using
              boundedVariation_generator_eq_drift_integral X hBV w x
    _ = X.c * deriv w x +
          ((∫ y in Ioo (-1 : ℝ) 0, w (x + y) - w x ∂X.ν) -
           (∫ y in Ioo (-1 : ℝ) 0, deriv w x * y ∂X.ν) +
           (∫ y in Iic (-1 : ℝ), w (x + y) - w x ∂X.ν)) := by
             rw [hJ, hSgen, hLgen]
    _ = (X.c * deriv w x -
           ∫ y in Ioo (-1 : ℝ) 0, deriv w x * y ∂X.ν) +
          ((∫ y in Ioo (-1 : ℝ) 0, w (x + y) - w x ∂X.ν) +
           (∫ y in Iic (-1 : ℝ), w (x + y) - w x ∂X.ν)) := by ring
    _ = X.drift * deriv w x +
          ∫ y in Iio (0 : ℝ), w (x + y) - w x ∂X.ν := by
            rw [hDrift, ← hVal]
