-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_eq_q_ae_of_gaussian_residual_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T22:42:00.485947+00:00
-- url     : https://prove2.me/submissions/1246b745-1c96-40e9-a6fd-3ee9d21134ba

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_ae_of_laplace_residual_vanishing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Almost-everywhere q-harmonicity of the scale function in the Gaussian case.

A single Laplace parameter does not identify the residual; one needs a whole
family of admissible parameters.  Because the Gaussian coefficient is positive,
the Levy exponent `X.psi` eventually exceeds every fixed discount rate, so the
admissible parameters of the scale-function Laplace identity contain a whole
half-line.  The uniqueness theorem for the Laplace transform of the generator
residual then applies.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hσ : 0 < X.σ)
    (hcont : ContinuousOn (fun x : ℝ => X.generator W x - q * W x) (Ioi 0))
    (hweighted : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0) :
    ∀ᵐ x ∂(volume.restrict (Ioo 0 a)),
      X.generator W x - q * W x = 0 := by
  obtain ⟨β0, hβ0, hψ⟩ := psi_eventually_gt_of_gaussian X q hσ
  have hfamily : ∀ θ : ℝ, β0 < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0 := by
    intro θ hθ
    have hθ0 : 0 ≤ θ := le_trans hβ0 (le_of_lt hθ)
    have hθψ : q < X.ψ θ := hψ θ (le_of_lt hθ)
    exact hweighted θ hθ0 hθψ
  exact scaleFunction_generator_eq_q_ae_of_laplace_residual_vanishing
    X q W hW a ha β0 hcont hfamily
