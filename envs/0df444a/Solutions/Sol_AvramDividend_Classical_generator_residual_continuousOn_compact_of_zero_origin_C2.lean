-- Prove2me | solution 1 for AvramDividend.Classical.generator_residual_continuousOn_compact_of_zero_origin_C2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:28:54.859808+00:00
-- url     : https://prove2.me/submissions/1b83b883-ce06-41ff-b644-72ef1cf6e455

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_compact_of_C2_jump_continuity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorJump_continuousOn_compact_of_zero_origin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ContinuousOn
      (fun x : ℝ => X.generator W x - q * W x)
      (Icc l u) := by
  exact generator_residual_continuousOn_compact_of_C2_jump_continuity
    X q W a l u hl hlu hu hC2
    (scaleFunction_generatorJump_continuousOn_compact_of_zero_origin
      X q W hW hzero a l u hl hlu hu hC2)
