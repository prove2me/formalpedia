-- Prove2me | solution 9 for AvramDividend.Classical.zero_cap_boundary_value_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T15:05:52.143927+00:00
-- url     : https://prove2.me/submissions/797268a9-c564-4aba-b14a-6325f4fab631

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_zero_nonneg
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_value_identity
import Theorems.Thm_AvramDividend_Classical_zero_cap_value_at_zero_upper_bound_of_boundary

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    0 ≤ barrierValue W 0 0 ∧
      valueFunctionLe X q 0 0 ≤ ENNReal.ofReal (barrierValue W 0 0) := by
  refine ⟨?_, ?_⟩
  · exact AvramDividend.Classical.barrierValue_zero_zero_nonneg X hX q hq W hW
  · have hboundary : dividendValue X q 0 (barrierStrategy X 0 0) =
        ENNReal.ofReal (barrierValue W 0 0) :=
      AvramDividend.Classical.barrierStrategy_zero_boundary_value_identity
        X hX q hq W hW
    exact AvramDividend.Classical.zero_cap_value_at_zero_upper_bound_of_boundary
      X hX q hq W hboundary

-- Fresh submission attempt 2026-10-28: identical mathematics, fresh snapshot bytes.
