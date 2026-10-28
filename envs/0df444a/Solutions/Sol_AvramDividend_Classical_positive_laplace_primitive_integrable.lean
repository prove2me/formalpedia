-- Prove2me | solution 1 for AvramDividend.Classical.positive_laplace_primitive_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:14:16.524763+00:00
-- url     : https://prove2.me/submissions/b9f126c9-cd26-480a-a4af-24fc8193dc65

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_laplace_constant_reference
import Theorems.Thm_AvramDividend_Classical_positive_weighted_causal_convolution_integrable
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- A positive-axis primitive inherits exponential integrability. -/
theorem solution
    (f : ℝ → ℝ) (θ : ℝ) (hθ : 0 < θ)
    (hf : IntegrableOn (fun s : ℝ => Real.exp (-(θ * s)) * f s)
      (Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
      (∫ s in Ioc (0 : ℝ) x, f s ∂volume))
      (Ioi (0 : ℝ)) volume := by
  have hconst : IntegrableOn
      (fun t : ℝ => Real.exp (-(θ * t)) * (1 : ℝ))
      (Ioi (0 : ℝ)) volume := by
    simpa only [mul_one] using (positive_laplace_constant_reference θ hθ).1
  simpa only [mul_one] using
    (positive_weighted_causal_convolution_integrable
      f (fun _ : ℝ => (1 : ℝ)) θ hf hconst)
