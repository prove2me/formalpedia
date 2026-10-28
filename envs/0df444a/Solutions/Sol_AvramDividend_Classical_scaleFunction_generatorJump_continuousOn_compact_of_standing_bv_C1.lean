-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorJump_continuousOn_compact_of_standing_bv_C1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:00:17.015758+00:00
-- url     : https://prove2.me/submissions/0ce186ba-48ab-45fc-9c7c-256fa918d57a

import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_uniform_linear_jump_bound_on_compact_C1
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorJump_continuousOn_compact_of_standing_bv_C1_of_linear_envelope
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The unconditional BV C1 jump-integral continuity theorem on compact intervals. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC1 : ContDiffOn ℝ 1 W (Ioo 0 a)) :
    ContinuousOn
      (fun x : ℝ =>
        ∫ y : ℝ, SpectrallyNegativeLevy.generatorIntegrand W x y
          ∂(X.ν.restrict (Iio 0)))
      (Icc l u) := by
  exact scaleFunction_generatorJump_continuousOn_compact_of_standing_bv_C1_of_linear_envelope
    X hX hbv q W hW a l u hl hlu hu hC1
    (scaleFunction_uniform_linear_jump_bound_on_compact_C1
      X q W hW a l u hl hlu hu hC1)
