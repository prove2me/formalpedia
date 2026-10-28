-- Prove2me | solution 6 for AvramDividend.Classical.scaleFunction_contDiff_one_of_unbounded_variation_nonpositive_q
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T03:56:33.076328+00:00
-- url     : https://prove2.me/submissions/22921ae9-70e9-4b4a-a3f9-273461690a4f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_scaleFunction_negative_q_impossible
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_C1_zero_discount_core

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq0 : q ≤ 0) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  rcases lt_or_eq_of_le hq0 with hneg | heq
  · exact False.elim
      (AvramDividend.Classical.unbounded_scaleFunction_negative_q_impossible
        X q hneg W hW hnbv)
  · subst heq
    exact AvramDividend.Classical.unbounded_scale_C1_zero_discount_core
      X W hW hnbv
