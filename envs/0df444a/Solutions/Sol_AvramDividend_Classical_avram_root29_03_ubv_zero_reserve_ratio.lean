-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_ubv_zero_reserve_ratio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:15:18.083067+00:00
-- url     : https://prove2.me/submissions/b66a8a91-1686-4c27-ac01-4739123edafb

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_zero_start_exit_ratio_of_near_zero
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The genuine original-clock two-sided exit ratio at the zero-reserve
endpoint needs no separate path-regularity hypothesis under UBV. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) :
    twoSidedExitExpectation X q a 0 =
      ENNReal.ofReal (W 0 / W a) := by
  exact chat04_unbounded_zero_start_exit_ratio_of_near_zero
    X hnbv q hq W hW a ha
    (ae_negative_near_zero_of_unbounded_variation X hnbv)
