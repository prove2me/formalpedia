-- Prove2me | solution 11 for AvramDividend.Classical.barrier_zero_boundary_value_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T04:39:31.75298+00:00
-- url     : https://prove2.me/submissions/025cc9e3-de31-4aa6-b6f1-cff36631a625

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_boundary_nonneg
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_value_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    0 ≤ barrierValue W 0 0 ∧
      dividendValue X q 0 (barrierStrategy X 0 0) =
        ENNReal.ofReal (barrierValue W 0 0) := by
  have hA : 0 ≤ barrierValue W 0 0 :=
    AvramDividend.Classical.barrierValue_zero_boundary_nonneg X hX q hq W hW
  have hB : dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) :=
    AvramDividend.Classical.barrierStrategy_zero_boundary_value_identity X hX q hq W hW
  exact ⟨hA, hB⟩
