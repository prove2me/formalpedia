-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_zero_boundary_value_identity_bv_case
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T13:28:14.470919+00:00
-- url     : https://prove2.me/submissions/18ba200c-551c-4281-bec3-3871c5f3f575

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_value_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The independently proved general true zero-barrier identity also holds in
    the bounded-variation branch. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation) :
    dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) := by
  exact barrierStrategy_zero_boundary_value_identity X hX q hq W hW
