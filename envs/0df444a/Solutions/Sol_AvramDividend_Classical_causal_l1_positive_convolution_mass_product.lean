-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_positive_convolution_mass_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:28:26.174751+00:00
-- url     : https://prove2.me/submissions/eb7859a4-c9aa-4e92-a1fa-b077a9203724

import Mathlib.Analysis.Convolution
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_laplace_product

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- The positive-time mass of an L1 causal convolution is multiplicative. -/
theorem solution
    (K F : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hF : IntegrableOn F (Ioi (0 : ℝ)) volume) :
    (∫ x in Ioi (0 : ℝ),
      (∫ s in Ioc (0 : ℝ) x, K s * F (x - s) ∂volume) ∂volume) =
      (∫ t in Ioi (0 : ℝ), K t ∂volume) *
      (∫ t in Ioi (0 : ℝ), F t ∂volume) := by
  have hK0 : IntegrableOn (fun t : ℝ => Real.exp (-(0 * t)) * K t)
      (Ioi (0 : ℝ)) volume := by simpa using hK
  have hF0 : IntegrableOn (fun t : ℝ => Real.exp (-(0 * t)) * F t)
      (Ioi (0 : ℝ)) volume := by simpa using hF
  simpa using
    (AvramDividend.Classical.positive_causal_convolution_laplace_product
      K F 0 hK0 hF0)
