-- Prove2me | solution 1 for AvramDividend.Classical.chat04_pointwise_discounted_strict_lowerfirst_joint_relative_barrier_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T12:02:51.605176+00:00
-- url     : https://prove2.me/submissions/1a4aa789-6568-46c2-bb25-d233dd5e5e47

import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_clocks_relative_barrier_comparison

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Increasing reserve and discount jointly reduces every strict discounted ruin-before-upper-exit reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q₁ q₂ a b x y : ℝ) (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂)
    (hxy : x ≤ y) (hrel : b - y ≤ a - x) (ω : Ω) :
    (if twoSidedExitDownTime X (-y) ω < twoSidedExitUpTime X (b - y) ω then
       ENNReal.ofReal (Real.exp
         (-(q₂ * ENNReal.toReal (twoSidedExitDownTime X (-y) ω))))
     else 0) ≤
    (if twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a - x) ω then
       ENNReal.ofReal (Real.exp
         (-(q₁ * ENNReal.toReal (twoSidedExitDownTime X (-x) ω))))
     else 0) := by
  obtain ⟨hup, hdown⟩ :=
    chat04_strict_exit_clocks_relative_barrier_comparison
      X a b x y hxy hrel ω
  by_cases hy : twoSidedExitDownTime X (-y) ω <
      twoSidedExitUpTime X (b - y) ω
  · have hx : twoSidedExitDownTime X (-x) ω <
        twoSidedExitUpTime X (a - x) ω :=
      lt_of_le_of_lt hdown (lt_of_lt_of_le hy hup)
    simp only [if_pos hy, if_pos hx]
    have hyTop : twoSidedExitDownTime X (-y) ω ≠ ⊤ :=
      ne_top_of_lt hy
    have hreal : ENNReal.toReal (twoSidedExitDownTime X (-x) ω) ≤
        ENNReal.toReal (twoSidedExitDownTime X (-y) ω) :=
      ENNReal.toReal_mono hyTop hdown
    have hmul1 := mul_le_mul_of_nonneg_left hreal hq₁
    have hmul2 : q₁ * ENNReal.toReal (twoSidedExitDownTime X (-y) ω) ≤
        q₂ * ENNReal.toReal (twoSidedExitDownTime X (-y) ω) :=
      mul_le_mul_of_nonneg_right hq ENNReal.toReal_nonneg
    exact ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr (neg_le_neg (le_trans hmul1 hmul2)))
  · simp only [if_neg hy]
    exact bot_le
