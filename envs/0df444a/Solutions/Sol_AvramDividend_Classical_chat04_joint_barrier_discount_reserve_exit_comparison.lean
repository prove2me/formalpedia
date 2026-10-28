-- Prove2me | solution 1 for AvramDividend.Classical.chat04_joint_barrier_discount_reserve_exit_comparison
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T10:31:25.57235+00:00
-- url     : https://prove2.me/submissions/fa5102e7-c319-412e-9293-5d350d86de2c

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_joint_barrier_discount_exit_antitone
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_strict_exit_monotone_initial_reserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- A harder upper barrier, higher discount and smaller initial reserve jointly reduce the strict exit transform. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q₁ q₂ a b x y : ℝ)
    (hq₁ : 0 ≤ q₁) (hqq : q₁ ≤ q₂)
    (hab : a ≤ b) (hxy : x ≤ y) :
    twoSidedExitExpectation X q₂ b x ≤
      twoSidedExitExpectation X q₁ a y := by
  exact le_trans
    (chat04_joint_barrier_discount_exit_antitone X q₁ q₂ a b x hq₁ hqq hab)
    (chat04_discounted_strict_exit_monotone_initial_reserve X q₁ a x y hq₁ hxy)
