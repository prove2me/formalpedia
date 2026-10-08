-- Prove2me | solution 1 for AvramDividend.Classical.generator_residual_integrableOn_compact_of_standing_bv_C2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T11:09:44.019808+00:00
-- url     : https://prove2.me/submissions/11d1b633-8f26-4a87-a4c9-7d6cfe278400

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_compact_of_standing_bv_C2
import Theorems.Thm_AvramDividend_Classical_integrableOn_Icc_of_continuousOn_finite_measure

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
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IntegrableOn (fun x : ℝ => X.generator W x - q * W x)
      (Icc l u) μ := by
  exact integrableOn_Icc_of_continuousOn_finite_measure
    (fun x : ℝ => X.generator W x - q * W x) μ l u hlu.le
    (generator_residual_continuousOn_compact_of_standing_bv_C2
      X hX hbv q W hW a l u hl hlu hu hC2)
