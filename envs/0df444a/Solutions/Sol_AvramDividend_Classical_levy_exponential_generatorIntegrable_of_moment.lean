-- Prove2me | solution 1 for AvramDividend.Classical.levy_exponential_generatorIntegrable_of_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:10:14.815878+00:00
-- url     : https://prove2.me/submissions/3dd214f1-b4a2-4702-b22f-decc8f229498

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_exp_compensated_jump_min_sq_bound
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_exp_mul

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ x : ℝ) (hθ : 0 ≤ θ)
    (hmoment : IntegrableOn
      (fun y : ℝ => min 1 (y ^ 2)) (Iio (0 : ℝ)) X.ν) :
    X.GeneratorIntegrable (fun z : ℝ => Real.exp (θ * z)) x := by
  rcases exp_compensated_jump_min_sq_bound θ hθ with ⟨C, -, hbound⟩
  have hmajor : IntegrableOn
      (fun y : ℝ => (Real.exp (θ * x) * C) * min 1 (y ^ 2))
      (Iio (0 : ℝ)) X.ν :=
    hmoment.const_mul (Real.exp (θ * x) * C)
  have hmprod : Measurable (fun y : ℝ => θ * y) :=
    measurable_const.mul measurable_id
  have hmexp : Measurable (fun y : ℝ => Real.exp (θ * y)) :=
    Real.measurable_exp.comp hmprod
  have hind : Measurable
      ((Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ))) :=
    measurable_const.indicator measurableSet_Ioo
  have hmkernel : Measurable (fun y : ℝ =>
      Real.exp (θ * y) - 1 - θ * y *
        (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y) :=
    (hmexp.sub measurable_const).sub (hmprod.mul hind)
  have hmeas : Measurable (fun y : ℝ =>
      Real.exp (θ * x) *
        (Real.exp (θ * y) - 1 - θ * y *
          (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)) :=
    measurable_const.mul hmkernel
  have heq :
      SpectrallyNegativeLevy.generatorIntegrand
        (fun z : ℝ => Real.exp (θ * z)) x =
        (fun y : ℝ => Real.exp (θ * x) *
          (Real.exp (θ * y) - 1 - θ * y *
            (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)) := by
    funext y
    exact generatorIntegrand_exp_mul θ x y
  change IntegrableOn
    (SpectrallyNegativeLevy.generatorIntegrand
      (fun z : ℝ => Real.exp (θ * z)) x) (Iio 0) X.ν
  rw [heq]
  apply Integrable.mono' hmajor hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := X.ν) (s := Iio (0 : ℝ))
    measurableSet_Iio] with y hy
  have hb := hbound y (mem_Iio.mp hy)
  change ‖Real.exp (θ * x) *
    (Real.exp (θ * y) - 1 - θ * y *
      (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)‖ ≤
    (Real.exp (θ * x) * C) * min 1 (y ^ 2)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  calc
    Real.exp (θ * x) *
        |Real.exp (θ * y) - 1 - θ * y *
          (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y| ≤
      Real.exp (θ * x) * (C * min 1 (y ^ 2)) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)
    _ = (Real.exp (θ * x) * C) * min 1 (y ^ 2) := by ring