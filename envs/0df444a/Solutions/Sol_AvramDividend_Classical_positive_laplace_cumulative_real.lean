-- Prove2me | solution 1 for AvramDividend.Classical.positive_laplace_cumulative_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T17:18:24.680773+00:00
-- url     : https://prove2.me/submissions/a1db3347-4add-405f-ac7d-5fffe12907a3

import Mathlib.Analysis.Convolution
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_real_laplace_causal_convolution
import Theorems.Thm_AvramDividend_Classical_positive_laplace_constant_reference

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

theorem solution
    (f : ℝ → ℝ) (θ : ℝ) (hθ : 0 < θ)
    (hf : IntegrableOn (fun s : ℝ => Real.exp (-(θ * s)) * f s)
      (Ioi (0 : ℝ)) volume) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      (∫ s in Ioc (0 : ℝ) x, f s ∂volume) ∂volume) =
      (∫ s in Ioi (0 : ℝ), Real.exp (-(θ * s)) * f s ∂volume) / θ := by
  obtain ⟨hci, hcv⟩ := positive_laplace_constant_reference θ hθ
  have hf' : IntegrableOn
      (fun s : ℝ => Real.exp (-θ * s) * f s)
      (Ioi (0 : ℝ)) volume := by
    simpa only [neg_mul] using hf
  have hci' : IntegrableOn
      (fun s : ℝ => Real.exp (-θ * s) * (1 : ℝ))
      (Ioi (0 : ℝ)) volume := by
    simpa only [mul_one, neg_mul] using hci
  have hcv' :
      (∫ s in Ioi (0 : ℝ), Real.exp (-θ * s) ∂volume) =
      1 / θ := by simpa only [neg_mul] using hcv
  have hconv := positive_real_laplace_causal_convolution
    f (fun _ : ℝ => 1) θ hf' hci'
  have hfactor :
      (∫ x in Ioi (0 : ℝ), ∫ s in Ioc (0 : ℝ) x,
        Real.exp (-θ * x) * f s ∂volume ∂volume) =
      (∫ s in Ioi (0 : ℝ), Real.exp (-θ * s) * f s ∂volume) *
        (1 / θ) := by
    simpa only [mul_one, hcv'] using hconv
  have hrewrite :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (∫ s in Ioc (0 : ℝ) x, f s ∂volume) ∂volume) =
      (∫ x in Ioi (0 : ℝ), ∫ s in Ioc (0 : ℝ) x,
        Real.exp (-θ * x) * f s ∂volume ∂volume) := by
    simp only [neg_mul, integral_const_mul]
  rw [hrewrite, hfactor]
  ring
