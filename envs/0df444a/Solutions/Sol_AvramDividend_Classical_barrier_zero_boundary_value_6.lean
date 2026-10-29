-- Prove2me | solution 6 for AvramDividend.Classical.barrier_zero_boundary_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:26:11.512415+00:00
-- url     : https://prove2.me/submissions/8061bf01-e8a5-42de-9372-ba3e041be0b8

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
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
    dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) := by
  exact barrierStrategy_zero_boundary_value_identity X hX q hq W hW
