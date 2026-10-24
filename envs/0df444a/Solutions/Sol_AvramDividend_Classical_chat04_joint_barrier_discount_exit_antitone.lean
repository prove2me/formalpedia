-- Prove2me | solution 1 for AvramDividend.Classical.chat04_joint_barrier_discount_exit_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:33:04.274617+00:00
-- url     : https://prove2.me/submissions/e62e2c38-a676-42af-9dd9-154737aa91b5

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_strict_exit_antitone_upper_barrier
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_antitone_discount
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Increasing the barrier and discount together decreases strict killed exit value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q₁ q₂ a b x : ℝ) (hq₁ : 0 ≤ q₁) (hqq : q₁ ≤ q₂) (hab : a ≤ b) :
    twoSidedExitExpectation X q₂ b x ≤ twoSidedExitExpectation X q₁ a x := by
  have hq₂ : 0 ≤ q₂ := le_trans hq₁ hqq
  exact le_trans
    (chat04_discounted_strict_exit_antitone_upper_barrier X q₂ a b x hq₂ hab)
    (chat04_twoSidedExitExpectation_antitone_discount X q₁ q₂ a x hqq)
