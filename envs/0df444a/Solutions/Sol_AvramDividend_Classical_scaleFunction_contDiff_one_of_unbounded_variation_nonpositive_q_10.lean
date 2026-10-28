-- Prove2me | solution 10 for AvramDividend.Classical.scaleFunction_contDiff_one_of_unbounded_variation_nonpositive_q
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:15:31.885556+00:00
-- url     : https://prove2.me/submissions/325705dc-5433-478d-9fc1-4e6a01e53385
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

-- Nonpositive-q C1 split: q=0 is the zero-discount core (Open), q<0 is
-- impossible under unbounded variation (Proved). Fresh case-split bytes.
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq0 : q ≤ 0) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  by_cases heq : q = 0
  · subst heq
    exact AvramDividend.Classical.unbounded_scale_C1_zero_discount_core X W hW hnbv
  · have hneg : q < 0 := lt_of_le_of_ne hq0 heq
    exact False.elim
      (AvramDividend.Classical.unbounded_scaleFunction_negative_q_impossible
        X q hneg W hW hnbv)
