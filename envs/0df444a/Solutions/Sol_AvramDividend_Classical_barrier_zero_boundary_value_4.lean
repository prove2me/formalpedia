-- Prove2me | solution 4 for AvramDividend.Classical.barrier_zero_boundary_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T07:56:37.139781+00:00
-- url     : https://prove2.me/submissions/ae95efaf-c2f4-4584-b0e3-4a3a24ce2c05

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_value_identity
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The legacy zero-barrier name is an alias of its canonical frontier proof. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) := by
  exact barrierStrategy_zero_boundary_value_identity X hX q hq W hW
