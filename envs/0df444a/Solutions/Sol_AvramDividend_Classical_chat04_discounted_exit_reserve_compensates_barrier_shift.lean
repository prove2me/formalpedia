-- Prove2me | solution 1 for AvramDividend.Classical.chat04_discounted_exit_reserve_compensates_barrier_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T10:41:43.493875+00:00
-- url     : https://prove2.me/submissions/7a4277c3-5054-460e-a5c5-681b6af9ed3c

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_clocks_relative_barrier_comparison

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- A reserve increase offsets a barrier increase when their relative upper threshold decreases. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a b x y : ℝ) (hq : 0 ≤ q)
    (hxy : x ≤ y) (hrel : b - y ≤ a - x) :
    twoSidedExitExpectation X q a x ≤
      twoSidedExitExpectation X q b y := by
  unfold twoSidedExitExpectation
  apply lintegral_mono
  intro ω
  obtain ⟨hup, hdown⟩ :=
    chat04_strict_exit_clocks_relative_barrier_comparison
      X a b x y hxy hrel ω
  change
    (if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
      ENNReal.ofReal (Real.exp
        (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
     else 0) ≤
    (if twoSidedExitUpTime X (b - y) ω < twoSidedExitDownTime X (-y) ω then
      ENNReal.ofReal (Real.exp
        (-(q * ENNReal.toReal (twoSidedExitUpTime X (b - y) ω))))
     else 0)
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
    have hmul := mul_le_mul_of_nonneg_left hreal hq
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hmul))
  · simp only [if_neg hx]
    exact bot_le
