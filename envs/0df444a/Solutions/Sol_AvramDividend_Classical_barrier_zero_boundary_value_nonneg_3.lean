-- Prove2me | solution 3 for AvramDividend.Classical.barrier_zero_boundary_value_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T19:07:18.047418+00:00
-- url     : https://prove2.me/submissions/cbb29ac5-b9ba-4012-b7dd-a79422671c1c

import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_boundary_nonneg
import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    0 ≤ barrierValue W 0 0 ∧
      dividendValue X q 0 (barrierStrategy X 0 0) =
        ENNReal.ofReal (barrierValue W 0 0) := by
  exact ⟨barrierValue_zero_boundary_nonneg X hX q hq W hW,
    barrier_zero_boundary_value X hX q hq W hW⟩
