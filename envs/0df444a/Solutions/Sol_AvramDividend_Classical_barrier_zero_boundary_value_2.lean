-- Prove2me | solution 2 for AvramDividend.Classical.barrier_zero_boundary_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T23:35:44.346984+00:00
-- url     : https://prove2.me/submissions/730ab5d1-72da-4806-83bc-ca6032d9bdd3

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_value_identity
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The zero-barrier payoff is the boundary identity for the reflected strategy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) := by
  exact barrierStrategy_zero_boundary_value_identity X hX q hq W hW
