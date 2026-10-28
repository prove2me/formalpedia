-- Prove2me | solution 1 for AvramDividend.Classical.chat04_pointwise_discounted_strict_exit_joint_relative_barrier_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:06:07.043225+00:00
-- url     : https://prove2.me/submissions/4a19717a-440d-433b-b4fd-cea914e35d9a

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_clocks_relative_barrier_comparison

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The killed discounted upper-exit payoff is jointly monotone under a reserve shift and discount increase. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q₁ q₂ a b x y : ℝ) (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂)
    (hxy : x ≤ y) (hrel : b - y ≤ a - x) (ω : Ω) :
    (if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
       ENNReal.ofReal (Real.exp
         (-(q₂ * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
     else 0) ≤
    (if twoSidedExitUpTime X (b - y) ω < twoSidedExitDownTime X (-y) ω then
       ENNReal.ofReal (Real.exp
         (-(q₁ * ENNReal.toReal (twoSidedExitUpTime X (b - y) ω))))
     else 0) := by
  obtain ⟨hup, hdown⟩ :=
    chat04_strict_exit_clocks_relative_barrier_comparison
      X a b x y hxy hrel ω
  by_cases hx : twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω
  · have hy : twoSidedExitUpTime X (b - y) ω <
        twoSidedExitDownTime X (-y) ω :=
      lt_of_le_of_lt hup (lt_of_lt_of_le hx hdown)
    simp only [if_pos hx, if_pos hy]
    have hxTop : twoSidedExitUpTime X (a - x) ω ≠ ⊤ :=
      ne_top_of_lt hx
    have hreal : ENNReal.toReal (twoSidedExitUpTime X (b - y) ω) ≤
        ENNReal.toReal (twoSidedExitUpTime X (a - x) ω) :=
      ENNReal.toReal_mono hxTop hup
    have hmul1 := mul_le_mul_of_nonneg_left hreal hq₁
    have hmul2 : q₁ * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω) ≤
        q₂ * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω) :=
      mul_le_mul_of_nonneg_right hq ENNReal.toReal_nonneg
    exact ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr (neg_le_neg (le_trans hmul1 hmul2)))
  · simp only [if_neg hx]
    exact bot_le
