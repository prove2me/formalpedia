-- Prove2me | solution 1 for AvramDividend.Classical.bv_signed_generator_kernel_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:57:07.304875+00:00
-- url     : https://prove2.me/submissions/5791ee01-17cb-49d9-874c-66eba83f3624

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_signed_generator_kernel_ae_measurable_negative
import Theorems.Thm_AvramDividend_Classical_bv_signed_generator_kernel_product_integrable_of_measurability
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Full BV signed generator-kernel product integrability without measurability assumptions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hWmon : Monotone W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) :
    Integrable (fun p : ℝ × ℝ =>
      Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ)))) := by
  have hAEm :=
    bv_signed_generator_kernel_ae_measurable_negative X W hWmon θ
  exact bv_signed_generator_kernel_product_integrable_of_measurability
    X hbv q W hW hWmon θ hθ hqθ hAEm
