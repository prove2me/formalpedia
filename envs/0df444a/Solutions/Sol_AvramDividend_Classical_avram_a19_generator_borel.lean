-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_generator_borel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T13:18:44.527423+00:00
-- url     : https://prove2.me/submissions/fc3931c9-e8dd-4879-ac24-ec1e41234f4e

import Mathlib
import Mathlib.Probability.Kernel.MeasurableIntegral
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_ruin_extension_value_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_levy_negative_mark_sigmaFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original source generator is Borel: its derivatives are measurable,
and its compensated negative-jump integral is a measurable parameter integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    Measurable (fun y : ℝ => X.generator w y) := by
  have hw : Measurable w :=
    avram_p3_e_compensator_original_ruin_extension_value_measurable w hw_cont hw_neg
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
      (fun y : ℝ => ∫ z : ℝ, SpectrallyNegativeLevy.generatorIntegrand w y z ∂κ y) := by
    funext y
    rfl
  have hSource : Measurable (fun y : ℝ =>
      ∫ z in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) := by
    rw [hEq]
    exact hInt.measurable
  have hGenEq :
      (fun y : ℝ => X.generator w y) =
      (fun y : ℝ => X.c * deriv w y +
        ∫ z in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) := by
    funext y
    simp [SpectrallyNegativeLevy.generator, hBV.1]
  rw [hGenEq]
  exact (measurable_const.mul hd).add hSource
