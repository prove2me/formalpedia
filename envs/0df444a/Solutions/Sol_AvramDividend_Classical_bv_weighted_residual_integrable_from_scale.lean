-- Prove2me | solution 1 for AvramDividend.Classical.bv_weighted_residual_integrable_from_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:44:19.815598+00:00
-- url     : https://prove2.me/submissions/303f5027-5dac-4833-b527-2a9ce8c0d4d1

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_deriv_integrable_positive_halfline
import Theorems.Thm_AvramDividend_Classical_bv_signed_generator_kernel_product_integrable
import Theorems.Thm_AvramDividend_Classical_bv_weighted_jump_integrable_of_product_integrable
import Theorems.Thm_AvramDividend_Classical_bv_weighted_generator_residual_integrable_of_components

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Assemble derivative, signed-jump and scale integrability into a generator residual bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hWmon : Monotone W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hWint : IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * W x) (Ioi (0 : ℝ))) :
    IntegrableOn (fun x : ℝ =>
      Real.exp (-(θ * x)) * (X.generator W x - q * W x))
      (Ioi (0 : ℝ)) := by
  have hDint :=
    chat07_scale_weighted_deriv_integrable_positive_halfline
      X q W hW θ hθ hqθ
  have hprod :=
    bv_signed_generator_kernel_product_integrable
      X hbv q W hW hWmon θ hθ hqθ
  have hJint :=
    bv_weighted_jump_integrable_of_product_integrable X θ W hprod
  exact bv_weighted_generator_residual_integrable_of_components
    X hbv q θ W hDint hJint hWint
