-- Prove2me | solution 7 for AvramDividend.Classical.zero_cap_value_at_zero_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:07:03.832875+00:00
-- url     : https://prove2.me/submissions/7dc5d03b-bf64-4a07-b027-286a4c49e9e6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound_of_boundary
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_value_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    valueFunctionLe X q 0 0 ≤ ENNReal.ofReal (barrierValue W 0 0) := by
  have hbound : dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) :=
    AvramDividend.Classical.barrierStrategy_zero_boundary_value_identity X hX q hq W hW
  exact AvramDividend.Classical.zero_cap_value_at_zero_upper_bound_of_boundary X hX q hq W hbound
