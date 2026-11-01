-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_far_field_jump_integral_exact_large_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:48:01.962978+00:00
-- url     : https://prove2.me/submissions/41a39f32-760b-432d-b868-f954276c951d

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_generatorIntegrable_strictly_above_real_cstar
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_generatorIntegrand_far_field_exact_large_jump_kernel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The actual compensated Lévy jump integral reduces exactly to the finite-measure
large-jump tail at far-field reserves, with crossing jumps retained. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (x : ℝ) (hfar : (cstar W).toReal + 1 ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      (∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ∂X.ν) =
      ∫ y in Iic (-1 : ℝ),
        (vcstar W (x + y) - vcstar W x) ∂X.ν := by
  have hx : (cstar W).toReal < x := by linarith
  refine ⟨vcstar_generatorIntegrable_strictly_above_real_cstar
      X q W hW x hx, ?_⟩
  rw [← MeasureTheory.integral_indicator measurableSet_Iio]
  rw [← MeasureTheory.integral_indicator measurableSet_Iic]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall (fun y : ℝ => by
    by_cases hy : y < 0
    · have hyI : y ∈ Iio (0 : ℝ) := hy
      rw [Set.indicator_of_mem hyI]
      rw [avram_wave4_05_source_generatorIntegrand_far_field_exact_large_jump_kernel
        W x y hfar hy]
      by_cases hlarge : y ≤ -1
      · have hyL : y ∈ Iic (-1 : ℝ) := hlarge
        simp [hlarge, Set.indicator_of_mem hyL]
      · have hnotL : y ∉ Iic (-1 : ℝ) := hlarge
        simp [hlarge, Set.indicator_of_notMem hnotL]
    · have hnotI : y ∉ Iio (0 : ℝ) := by
        simpa only [mem_Iio] using hy
      have hnotL : y ∉ Iic (-1 : ℝ) := by
        intro hyL
        have hyLe : y ≤ -1 := hyL
        linarith
      simp [Set.indicator_of_notMem hnotI,
        Set.indicator_of_notMem hnotL])
