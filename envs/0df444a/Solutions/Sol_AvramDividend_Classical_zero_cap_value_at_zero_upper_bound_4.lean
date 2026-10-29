-- Prove2me | solution 4 for AvramDividend.Classical.zero_cap_value_at_zero_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T23:32:27.622064+00:00
-- url     : https://prove2.me/submissions/373375f9-be05-4e06-b90b-457b5a1365db

import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound_of_boundary
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_value_identity
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Reduce the optimal zero-cap value inequality to the barrier boundary identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    valueFunctionLe X q 0 0 ≤ ENNReal.ofReal (barrierValue W 0 0) := by
  exact zero_cap_value_at_zero_upper_bound_of_boundary X hX q hq W
    (barrierStrategy_zero_boundary_value_identity X hX q hq W hW)
