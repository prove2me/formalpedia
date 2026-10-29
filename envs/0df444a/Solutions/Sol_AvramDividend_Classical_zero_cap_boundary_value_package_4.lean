-- Prove2me | solution 4 for AvramDividend.Classical.zero_cap_boundary_value_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T06:19:23.938335+00:00
-- url     : https://prove2.me/submissions/9611ea1d-8cbd-4baa-88df-97d02984b2df

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_boundary_nonneg
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_value_identity
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound_of_boundary

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
    0 ≤ barrierValue W 0 0 ∧
      valueFunctionLe X q 0 0 ≤ ENNReal.ofReal (barrierValue W 0 0) := by
  have hleft : 0 ≤ barrierValue W 0 0 :=
    AvramDividend.Classical.barrierValue_zero_boundary_nonneg X hX q hq W hW
  have hbound : dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) :=
    AvramDividend.Classical.barrierStrategy_zero_boundary_value_identity X hX q hq W hW
  have hright : valueFunctionLe X q 0 0 ≤ ENNReal.ofReal (barrierValue W 0 0) :=
    AvramDividend.Classical.zero_cap_value_at_zero_upper_bound_of_boundary X hX q hq W hbound
  exact ⟨hleft, hright⟩
