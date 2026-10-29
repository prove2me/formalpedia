-- Prove2me | solution 8 for AvramDividend.Classical.barrier_zero_boundary_value_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:22:54.699335+00:00
-- url     : https://prove2.me/submissions/90dbf398-a602-4318-ad2b-10f029f98136

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_boundary_nonneg
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
    0 ≤ barrierValue W 0 0 ∧
      dividendValue X q 0 (barrierStrategy X 0 0) =
        ENNReal.ofReal (barrierValue W 0 0) := by
  exact ⟨
    AvramDividend.Classical.barrierValue_zero_boundary_nonneg X hX q hq W hW,
    AvramDividend.Classical.barrierStrategy_zero_boundary_value_identity X hX q hq W hW⟩
