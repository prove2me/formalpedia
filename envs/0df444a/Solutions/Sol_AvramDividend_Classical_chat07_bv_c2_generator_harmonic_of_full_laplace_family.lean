-- Prove2me | solution 1 for AvramDividend.Classical.chat07_bv_c2_generator_harmonic_of_full_laplace_family
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T17:54:18.183479+00:00
-- url     : https://prove2.me/submissions/fa4bf000-600d-4be3-aece-48d02a53b1ce

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_Ioi_of_standing_bv_C2
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_interval_harmonic_of_laplace_family
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! BV regularity and the full Laplace residual family imply local q-harmonicity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hC1 : ContDiffOn ℝ 1 W (Ioi 0))
    (hC2 : ContDiffOn ℝ 2 W (Ioi 0))
    (hweighted : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0) :
    ∀ x ∈ Ioo 0 a,
      X.GeneratorIntegrable W x ∧
        X.generator W x - q * W x = 0 := by
  have hcont : ContinuousOn
      (fun x : ℝ => X.generator W x - q * W x) (Ioi 0) :=
    generator_residual_continuousOn_Ioi_of_standing_bv_C2
      X hX hbv q W hW hC2
  have hint : ∀ x ∈ Ioo 0 a, X.GeneratorIntegrable W x := by
    intro x hx
    exact scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
      X q W hW hbv x hx.1 hC1
  exact scaleFunction_generator_interval_harmonic_of_laplace_family
    X hX q hq W hW a ha hcont hweighted hint
