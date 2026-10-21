-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_interval_harmonic_of_laplace_family
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T21:41:18.445041+00:00
-- url     : https://prove2.me/submissions/4cc873d3-87c7-4387-b80c-283ce48dd26b

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_q_ae_of_weighted_residual_vanishing_standing
import Theorems.Thm_AvramDividend_Classical_generator_eq_q_on_Ioo_of_ae_zero_and_continuousOn
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

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
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hcont : ContinuousOn (fun x : ℝ => X.generator W x - q * W x)
      (Ioi (0 : ℝ)))
    (hweighted : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0)
    (hint : ∀ x ∈ Ioo 0 a, X.GeneratorIntegrable W x) :
    ∀ x ∈ Ioo 0 a,
      X.GeneratorIntegrable W x ∧
        X.generator W x - q * W x = 0 := by
  have hae : ∀ᵐ x ∂(volume.restrict (Ioo 0 a)),
      X.generator W x - q * W x = 0 :=
    scaleFunction_generator_eq_q_ae_of_weighted_residual_vanishing_standing
      X hX q hq W hW a ha hcont hweighted
  have hcontI : ContinuousOn
      (fun x : ℝ => X.generator W x - q * W x) (Ioo 0 a) := by
    apply hcont.mono
    intro x hx
    exact hx.1
  have heq : ∀ x ∈ Ioo 0 a,
      X.generator W x - q * W x = 0 :=
    generator_eq_q_on_Ioo_of_ae_zero_and_continuousOn
      X q W a hcontI hae
  intro x hx
  exact ⟨hint x hx, heq x hx⟩
