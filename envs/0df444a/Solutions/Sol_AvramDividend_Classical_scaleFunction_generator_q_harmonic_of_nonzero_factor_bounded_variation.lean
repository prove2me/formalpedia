-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generator_q_harmonic_of_nonzero_factor_bounded_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:04:38.176755+00:00
-- url     : https://prove2.me/submissions/3e42bcaa-5c8e-4ff9-bca6-dff77b658bdf

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_one_of_boundedVariation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_interval_harmonic_of_bv_C1_weighted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Under bounded variation, combine scale C1 regularity, integrability, and the
weighted-residual uniqueness theorem on the positive optimal-barrier interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W)
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0)
    (hweighted : ∀ θ : ℝ, 0 ≤ θ → q < X.ψ θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) (Ioi (0 : ℝ)) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        (X.generator W x - q * W x)) = 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x ∧
        X.generator W x - q * W x = 0 := by
  intro x hx
  have ha : 0 < (cstar W).toReal := lt_trans hx.1 hx.2
  have hC1 : ContDiffOn ℝ 1 W (Ioi 0) :=
    scaleFunction_contDiffOn_one_of_boundedVariation X hX q hq W hW hbv
  have hint : ∀ y ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W y := by
    intro y hy
    exact scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
      X q W hW hbv y hy.1 hC1
  exact scaleFunction_generator_interval_harmonic_of_bv_C1_weighted
    X hX hbv q hq W hW (cstar W).toReal ha hweighted hint x hx
