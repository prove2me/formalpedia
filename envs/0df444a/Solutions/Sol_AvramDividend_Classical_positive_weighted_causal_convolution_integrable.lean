-- Prove2me | solution 1 for AvramDividend.Classical.positive_weighted_causal_convolution_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T17:23:39.054071+00:00
-- url     : https://prove2.me/submissions/0030490a-3b2d-461f-8eca-712b0f6dbb42

import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_laplace_integrable
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

theorem solution
    (f g : ℝ → ℝ) (θ : ℝ)
    (hf : IntegrableOn (fun s : ℝ => Real.exp (-(θ * s)) * f s)
      (Ioi (0 : ℝ)) volume)
    (hg : IntegrableOn (fun t : ℝ => Real.exp (-(θ * t)) * g t)
      (Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
      (∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume))
      (Ioi (0 : ℝ)) volume := by
  exact positive_causal_convolution_laplace_integrable f g θ hf hg
