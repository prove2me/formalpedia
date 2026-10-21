-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_eq_q_ae_of_weighted_residual_vanishing_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T15:25:23.114372+00:00
-- url     : https://prove2.me/submissions/14cf4064-662d-40cb-aa9e-18c76aed44ee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_ae_of_laplace_residual_vanishing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hcont : ContinuousOn (fun x : ℝ => X.generator W x - q * W x) (Ioi 0))
    (hweighted : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0) :
    ∀ᵐ x ∂(volume.restrict (Ioo 0 a)),
      X.generator W x - q * W x = 0 := by
  obtain ⟨β0, hβ0, hψ⟩ := psi_eventually_gt_of_standing X hX q hq
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
