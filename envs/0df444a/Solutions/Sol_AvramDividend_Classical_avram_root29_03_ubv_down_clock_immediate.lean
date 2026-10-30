-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_ubv_down_clock_immediate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T07:40:53.612571+00:00
-- url     : https://prove2.me/submissions/355498bf-591f-4d0b-8f02-1fc94859125d

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat04_down_exit_time_zero_of_negative_near_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Genuine unbounded-variation paths enter the strict negative half-line
instantaneously, expressed in the two-sided-exit clock of equation (3.6). -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation) :
    ∀ᵐ ω ∂P, twoSidedExitDownTime X 0 ω = 0 := by
  filter_upwards [ae_negative_near_zero_of_unbounded_variation X hnbv] with ω hnear
  simpa only [twoSidedExitDownTime] using
    (chat04_down_exit_time_zero_of_negative_near_zero X ω hnear)
