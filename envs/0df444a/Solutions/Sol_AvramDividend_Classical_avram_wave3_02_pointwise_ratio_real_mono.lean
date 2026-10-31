-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_pointwise_ratio_real_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:29:40.869146+00:00
-- url     : https://prove2.me/submissions/7f75021e-30f3-4d08-aaea-d99a4a5a8898

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_deriv_pos_of_pointwise_diff
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_mono_barrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_ratio_of_pointwise_diff_and_sandwich
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual real q-scale quotient increases between all positive
differentiability points, without assuming global C1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b)
    (hda : DifferentiableAt ℝ W a)
    (hdb : DifferentiableAt ℝ W b) :
    W a / deriv W a ≤ W b / deriv W b := by
  have hWb : 0 < W b :=
    scaleFunction_strict_pos_of_standing X hX q hq W hW b hb
  have hdbpos : 0 < deriv W b :=
    avram_wave3_02_deriv_pos_of_pointwise_diff
      X hX q hq W hW b hb hdb
  have hnonneg : 0 ≤ W b / deriv W b :=
    le_of_lt (div_pos hWb hdbpos)
  apply (ENNReal.ofReal_le_ofReal_iff hnonneg).mp
  calc
    ENNReal.ofReal (W a / deriv W a) = barrierSupValue X a q :=
      (avram_wave3_02_ratio_of_pointwise_diff_and_sandwich
        X hX q hq W hW a ha hda).symm
    _ ≤ barrierSupValue X b q := barrierSupValue_mono_barrier X a b q hab
    _ = ENNReal.ofReal (W b / deriv W b) :=
      avram_wave3_02_ratio_of_pointwise_diff_and_sandwich
        X hX q hq W hW b hb hdb
