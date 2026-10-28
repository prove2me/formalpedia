-- Prove2me | solution 3 for AvramDividend.Classical.scaleFunction_contDiff_one_of_unbounded_variation_nonpositive_q
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T00:33:24.33401+00:00
-- url     : https://prove2.me/submissions/14d3ef54-6026-4e5c-9589-bf8069725419
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
  -- Dichotomy on the discount sign (MATHEMATICAL_DECOMPOSITION):
  -- negative q is impossible for UBV scale functions (Proved d14a3b03),
  -- while q = 0 is exactly the Open zero-discount C1 core (8aaa16d2).
  rcases lt_or_eq_of_le hq0 with hneg | rfl
  · exact False.elim
      (AvramDividend.Classical.unbounded_scaleFunction_negative_q_impossible
        X q hneg W hW hnbv)
  · exact AvramDividend.Classical.unbounded_scale_C1_zero_discount_core
      X W hW hnbv
