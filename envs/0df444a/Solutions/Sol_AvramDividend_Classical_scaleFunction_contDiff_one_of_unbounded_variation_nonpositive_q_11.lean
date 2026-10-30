-- Prove2me | solution 11 for AvramDividend.Classical.scaleFunction_contDiff_one_of_unbounded_variation_nonpositive_q
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:40:41.635208+00:00
-- url     : https://prove2.me/submissions/5d7dfb2a-24ca-4e0e-8717-7d2774de976a
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

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

-- C1 for nonpositive q via zero-discount core vs negative-q impossibility.
-- Variant (2026-10-29): rcases on lt_or_eq_of_le instead of the prior by_cases +
-- lt_of_le_of_ne shape, so bytes and elaboration differ; mathematics unchanged.
-- q < 0 is vacuous via Proved d14a3b03; q = 0 closes via Open 8aaa16d2 core.
-- Still SKETCH_EXPECTED while 8aaa16d2 is Open. No local Lean was run.
-- ProofCheckpoint: MATHEMATICAL_DECOMPOSITION.
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq0 : q ≤ 0) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  rcases lt_or_eq_of_le hq0 with hlt | rfl
  · exact False.elim
      (AvramDividend.Classical.unbounded_scaleFunction_negative_q_impossible
        X q hlt W hW hnbv)
  · exact AvramDividend.Classical.unbounded_scale_C1_zero_discount_core
      X W hW hnbv
