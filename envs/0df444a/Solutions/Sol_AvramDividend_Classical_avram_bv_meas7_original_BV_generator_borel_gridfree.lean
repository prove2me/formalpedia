-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_original_BV_generator_borel_gridfree
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:41:00.172523+00:00
-- url     : https://prove2.me/submissions/251333e1-e97f-4e1a-9e56-dc24c7f15d92

import Mathlib
import Mathlib.Probability.Kernel.MeasurableIntegral
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Borel measurability of the original BV generator uses neither a grid nor a proxy source. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hw : Measurable w) :
    Measurable (fun y : ℝ => X.generator w y) := by
  have hd : Measurable (deriv w) := measurable_deriv w
  letI : SigmaFinite X.ν :=
    avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite X
  let μ : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  letI : SFinite μ := inferInstance
  let κ : ProbabilityTheory.Kernel ℝ ℝ :=
    ProbabilityTheory.Kernel.const ℝ μ
  letI : ProbabilityTheory.IsSFiniteKernel κ := by
    dsimp [κ]
    infer_instance
  have hcut : Measurable (fun z : ℝ =>
      (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) z) :=
    measurable_const.indicator measurableSet_Ioo
  have hF : Measurable (fun p : ℝ × ℝ =>
      SpectrallyNegativeLevy.generatorIntegrand w p.1 p.2) := by
    dsimp [SpectrallyNegativeLevy.generatorIntegrand]
    exact ((hw.comp (measurable_fst.add measurable_snd)).sub
      (hw.comp measurable_fst)).sub
      (((hd.comp measurable_fst).mul measurable_snd).mul
        (hcut.comp measurable_snd))
  have hInt : StronglyMeasurable (fun y : ℝ =>
      ∫ z : ℝ, SpectrallyNegativeLevy.generatorIntegrand w y z ∂κ y) :=
    hF.stronglyMeasurable.integral_kernel_prod_right'
  have hEq :
      (fun y : ℝ => ∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) =
      (fun y : ℝ => ∫ z : ℝ,
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂κ y) := by
    funext y
    rfl
  have hSource : Measurable (fun y : ℝ =>
      ∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) := by
    rw [hEq]
    exact hInt.measurable
  have hGenEq :
      (fun y : ℝ => X.generator w y) =
      (fun y : ℝ => X.c * deriv w y +
        ∫ z in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) := by
    funext y
    simp [SpectrallyNegativeLevy.generator, hBV.1]
  rw [hGenEq]
  exact (measurable_const.mul hd).add hSource
