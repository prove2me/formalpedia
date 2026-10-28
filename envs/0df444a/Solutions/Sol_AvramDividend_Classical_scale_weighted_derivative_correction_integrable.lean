-- Prove2me | solution 1 for AvramDividend.Classical.scale_weighted_derivative_correction_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:17:32.414207+00:00
-- url     : https://prove2.me/submissions/2415ede2-6fae-469b-bb23-4c668c18fc81

import Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_deriv_integrable_positive_halfline
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The derivative of an exponentially damped scale function is L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * (deriv W x - θ * W x))
      (Ioi (0 : ℝ)) volume := by
  have hD : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * deriv W x)
      (Ioi (0 : ℝ)) volume :=
    chat07_scale_weighted_deriv_integrable_positive_halfline
      X q W hW θ hθ hqθ
  have hWint : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * W x)
      (Ioi (0 : ℝ)) volume :=
    (hW.2.2.2.2 θ hθ hqθ).1
  have hsub : IntegrableOn
      (fun x : ℝ =>
        Real.exp (-(θ * x)) * deriv W x -
          θ * (Real.exp (-(θ * x)) * W x))
      (Ioi (0 : ℝ)) volume :=
    hD.sub (hWint.const_mul θ)
  convert hsub using 1
  ext x
  ring
