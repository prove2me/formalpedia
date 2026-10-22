-- Prove2me | solution 1 for AvramDividend.Classical.chat07_bv_cap_harmonic_from_regular_scale_and_interior
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:12:43.859956+00:00
-- url     : https://prove2.me/submissions/acdaf0eb-bd6f-4fc9-99b5-2ed94b3baf4e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat07_vcstar_pure_jump_cap_harmonic_of_differentiable_scale
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_Ioi_of_standing_bv_C2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! BV scale regularity supplies the domain and continuity at the cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (hσ : X.σ = 0)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (ha : 0 < (cstar W).toReal)
    (hWdiff : DifferentiableAt ℝ W (cstar W).toReal)
    (hWderiv : deriv W (cstar W).toReal ≠ 0)
    (hC1 : ContDiffOn ℝ 1 W (Ioi 0))
    (hC2 : ContDiffOn ℝ 2 W (Ioi 0))
    (hinside : ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.generator W x - q * W x = 0) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal = 0 := by
  have hdom : X.GeneratorIntegrable W (cstar W).toReal :=
    scaleFunction_generatorIntegrable_of_boundedVariation_contDiff_one
      X q W hW hbv (cstar W).toReal ha hC1
  have hcontIoi : ContinuousOn
      (fun x : ℝ => X.generator W x - q * W x) (Ioi 0) :=
    generator_residual_continuousOn_Ioi_of_standing_bv_C2
      X hX hbv q W hW hC2
  have hcont : ContinuousOn
      (fun x : ℝ => X.generator W x - q * W x)
      (Ioc 0 (cstar W).toReal) :=
    hcontIoi.mono (by
      intro x hx
      exact hx.1)
  exact chat07_vcstar_pure_jump_cap_harmonic_of_differentiable_scale
    X hσ q W hW.1 ha hWdiff hWderiv hdom hcont hinside
