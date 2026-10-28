-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_interval_harmonic_of_bv_C1_weighted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:31:00.196888+00:00
-- url     : https://prove2.me/submissions/50499043-169b-482a-b382-15e6e50ab260

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_one_of_boundedVariation
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_positive_of_standing_bv_C1_sigma_zero
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_interval_harmonic_of_laplace_family
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The first-order BV generator is harmonic wherever its weighted Laplace residual vanishes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hweighted : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0)
    (hint : ∀ x ∈ Ioo 0 a, X.GeneratorIntegrable W x) :
    ∀ x ∈ Ioo 0 a,
      X.GeneratorIntegrable W x ∧
        X.generator W x - q * W x = 0 := by
  have hσ : X.σ = 0 := hbv.1
  have hC1 : ContDiffOn ℝ 1 W (Ioi 0) :=
    scaleFunction_contDiffOn_one_of_boundedVariation X hX q hq W hW hbv
  have hcont : ContinuousOn
      (fun x : ℝ => X.generator W x - q * W x) (Ioi 0) :=
    generator_residual_continuousOn_positive_of_standing_bv_C1_sigma_zero
      X hX hbv hσ q W hW hC1
  exact scaleFunction_generator_interval_harmonic_of_laplace_family
    X hX q hq W hW a ha hcont hweighted hint
