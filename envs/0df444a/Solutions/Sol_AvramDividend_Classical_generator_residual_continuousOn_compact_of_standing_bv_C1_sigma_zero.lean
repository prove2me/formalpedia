-- Prove2me | solution 1 for AvramDividend.Classical.generator_residual_continuousOn_compact_of_standing_bv_C1_sigma_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:06:19.409869+00:00
-- url     : https://prove2.me/submissions/a11a1328-74bc-4827-997c-c416cc4d1c5a

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorJump_continuousOn_compact_of_standing_bv_C1
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_of_sigma_zero_components
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Continuity of the BV C1 generator residual on an interior compact interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation) (hσ : X.σ = 0)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC1 : ContDiffOn ℝ 1 W (Ioo 0 a)) :
    ContinuousOn (fun x : ℝ => X.generator W x - q * W x) (Icc l u) := by
  have hsub : Icc l u ⊆ Ioo (0 : ℝ) a := by
    intro z hz
    exact ⟨lt_of_lt_of_le hl hz.1, lt_of_le_of_lt hz.2 hu⟩
  have hWcont : ContinuousOn W (Icc l u) :=
    hC1.continuousOn.mono hsub
  have hDcont : ContinuousOn (deriv W) (Icc l u) :=
    (hC1.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hsub
  have hJcont : ContinuousOn
      (fun x : ℝ =>
        ∫ y in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)
      (Icc l u) :=
    scaleFunction_generatorJump_continuousOn_compact_of_standing_bv_C1
      X hX hbv q W hW a l u hl hlu hu hC1
  exact generator_residual_continuousOn_of_sigma_zero_components
    X hσ q W (Icc l u) hWcont hDcont hJcont
