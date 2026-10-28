-- Prove2me | solution 1 for AvramDividend.Classical.chat04_discounted_exit_relative_barrier_and_discount_comparison
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:06:05.771963+00:00
-- url     : https://prove2.me/submissions/774ce8d9-21e2-4650-bd7b-bca0870999bd

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_antitone_discount
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_exit_reserve_compensates_barrier_shift

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Increasing the discount rate and relative reserve preserves the killed-exit bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q₁ q₂ a b x y : ℝ)
    (hq : q₁ ≤ q₂) (hq₁ : 0 ≤ q₁)
    (hxy : x ≤ y) (hrel : b - y ≤ a - x) :
    twoSidedExitExpectation X q₂ a x ≤
      twoSidedExitExpectation X q₁ b y := by
  exact le_trans
    (chat04_twoSidedExitExpectation_antitone_discount X q₁ q₂ a x hq)
    (chat04_discounted_exit_reserve_compensates_barrier_shift
      X q₁ a b x y hq₁ hxy hrel)
