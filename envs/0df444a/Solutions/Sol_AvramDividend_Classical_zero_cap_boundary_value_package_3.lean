-- Prove2me | solution 3 for AvramDividend.Classical.zero_cap_boundary_value_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T23:33:31.454227+00:00
-- url     : https://prove2.me/submissions/5bb0e38c-8d75-47fb-928a-3f4cbcb63fda

import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_zero_nonneg
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

/-- Package the scale-value sign and zero-cap verification under a boundary identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    0 ≤ barrierValue W 0 0 ∧
      valueFunctionLe X q 0 0 ≤ ENNReal.ofReal (barrierValue W 0 0) := by
  exact ⟨barrierValue_zero_zero_nonneg X hX q hq W hW,
    zero_cap_value_at_zero_upper_bound_of_boundary X hX q hq W
      (barrierStrategy_zero_boundary_value_identity X hX q hq W hW)⟩
