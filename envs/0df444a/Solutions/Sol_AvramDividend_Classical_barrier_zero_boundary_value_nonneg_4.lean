-- Prove2me | solution 4 for AvramDividend.Classical.barrier_zero_boundary_value_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:13:48.344112+00:00
-- url     : https://prove2.me/submissions/54ee31b1-4644-4510-88d1-c815869511f9

import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_boundary_nonneg
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_zero_reflectedSupValue_eq_barrierValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The zero-barrier package reduces to the genuine reflected-supremum endpoint law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    0 ≤ barrierValue W 0 0 ∧
      dividendValue X q 0 (barrierStrategy X 0 0) =
        ENNReal.ofReal (barrierValue W 0 0) := by
  refine ⟨barrierValue_zero_boundary_nonneg X hX q hq W hW, ?_⟩
  calc
    dividendValue X q 0 (barrierStrategy X 0 0) =
        barrierSupValue X 0 q :=
      barrierValue_self_eq_barrierSupValue X q 0
    _ = ENNReal.ofReal (barrierValue W 0 0) :=
      zero_reflectedSupValue_eq_barrierValue X hX q hq W hW
