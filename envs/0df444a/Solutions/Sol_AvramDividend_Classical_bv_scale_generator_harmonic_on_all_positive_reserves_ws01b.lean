-- Prove2me | solution 1 for AvramDividend.Classical.bv_scale_generator_harmonic_on_all_positive_reserves_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T10:50:18.837733+00:00
-- url     : https://prove2.me/submissions/1dffcaec-fa18-45f3-984b-c7d75dd71ad7

import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_one_of_boundedVariation
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_positive_of_standing_bv_C1_sigma_zero
import Theorems.Thm_AvramDividend_Classical_bv_weighted_generator_residual_family_from_scale_20261026
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_interval_harmonic_of_laplace_family
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The BV scale function is q-harmonic at every positive capital level. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 < x →
      X.GeneratorIntegrable W x ∧ X.generator W x - q * W x = 0 := by
  have hC1 : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiffOn_one_of_boundedVariation X hX q hq W hW hbv
  have hσ : X.σ = 0 := hbv.1
  have hCont :
      ContinuousOn (fun y : ℝ => X.generator W y - q * W y) (Ioi (0 : ℝ)) :=
    generator_residual_continuousOn_positive_of_standing_bv_C1_sigma_zero
      X hX hbv hσ q W hW hC1
  have hWeighted :=
    bv_weighted_generator_residual_family_from_scale_20261026
      X hX hbv q hq W hW
  intro x hx
  have hA : 0 < x + 1 := by linarith
  have hInt :
      ∀ y ∈ Ioo (0 : ℝ) (x + 1), X.GeneratorIntegrable W y := by
    intro y hy
    exact scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
      X q W hW hbv y hy.1 hC1
  have hInterval :=
    scaleFunction_generator_interval_harmonic_of_laplace_family
      X hX q hq W hW (x + 1) hA hCont hWeighted hInt
  exact hInterval x ⟨hx, by linarith⟩
