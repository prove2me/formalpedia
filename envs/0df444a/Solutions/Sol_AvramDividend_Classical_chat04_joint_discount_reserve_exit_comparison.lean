-- Prove2me | solution 1 for AvramDividend.Classical.chat04_joint_discount_reserve_exit_comparison
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T10:31:21.273171+00:00
-- url     : https://prove2.me/submissions/4edefcc4-00bd-45fb-828d-d3f0744d46b6

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_antitone_discount
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_strict_exit_monotone_initial_reserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Raising the discount rate while lowering initial reserve weakens the strict two-sided exit transform. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q₁ q₂ a x y : ℝ)
    (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂) (hxy : x ≤ y) :
    twoSidedExitExpectation X q₂ a x ≤
      twoSidedExitExpectation X q₁ a y := by
  exact le_trans
    (chat04_twoSidedExitExpectation_antitone_discount X q₁ q₂ a x hq)
    (chat04_discounted_strict_exit_monotone_initial_reserve X q₁ a x y hq₁ hxy)
