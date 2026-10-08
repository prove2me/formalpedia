-- Prove2me | solution 1 for AvramDividend.Classical.generator_residual_continuousOn_Ioo_of_standing_bv_C2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T12:49:25.84824+00:00
-- url     : https://prove2.me/submissions/a78709b9-e75a-4dfd-83e7-4cd32aa32753

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioo_of_continuousOn_all_compact_subintervals
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_compact_of_standing_bv_C2

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
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ContinuousOn
      (fun x : ℝ => X.generator W x - q * W x)
      (Ioo 0 a) := by
  apply continuousOn_Ioo_of_continuousOn_all_compact_subintervals
    (fun x : ℝ => X.generator W x - q * W x) a ha
  intro l u hl hlu hu
  exact generator_residual_continuousOn_compact_of_standing_bv_C2
    X hX hbv q W hW a l u hl hlu hu hC2
