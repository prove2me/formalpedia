-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_generator_true_negative_integral_exact_large_small_unit_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:36:51.470189+00:00
-- url     : https://prove2.me/submissions/f18c6af8-626a-4c3c-bb80-49db425b09ed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (y : ℝ)
    (hGen : X.GeneratorIntegrable w y) :
    (∫ z in Iio (0 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) =
    (∫ z in Iic (-1 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) +
    (∫ z in Ioo (-1 : ℝ) 0,
      SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) := by
  let f : ℝ → ℝ :=
    SpectrallyNegativeLevy.generatorIntegrand w y
  have hFull : IntegrableOn f (Iio (0 : ℝ)) X.ν := hGen
  have hLarge : IntegrableOn f (Iic (-1 : ℝ)) X.ν :=
    hFull.mono_set (by
      intro z hz
      change z ≤ (-1 : ℝ) at hz
      change z < 0
      exact lt_of_le_of_lt hz (by norm_num))
  have hSmall : IntegrableOn f (Ioo (-1 : ℝ) 0) X.ν :=
    hFull.mono_set (by intro z hz; exact hz.2)
  have hd : Disjoint (Iic (-1 : ℝ)) (Ioo (-1 : ℝ) 0) := by
    apply Set.disjoint_left.mpr
    intro z hzL hzR
    exact (not_lt.mpr hzL) hzR.1
  have hUnion :
      Iic (-1 : ℝ) ∪ Ioo (-1 : ℝ) 0 = Iio (0 : ℝ) := by
    ext z
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioo, Set.mem_Iio]
    constructor
    · rintro (h | ⟨_, hz⟩)
      · linarith
      · exact hz
    · intro hz
      by_cases h : z ≤ -1
      · exact Or.inl h
      · exact Or.inr ⟨lt_of_not_ge h, hz⟩
  change (∫ z in Iio (0 : ℝ), f z ∂X.ν) =
    (∫ z in Iic (-1 : ℝ), f z ∂X.ν) +
    (∫ z in Ioo (-1 : ℝ) 0, f z ∂X.ν)
  rw [← hUnion]
  exact setIntegral_union hd measurableSet_Ioo hLarge hSmall
