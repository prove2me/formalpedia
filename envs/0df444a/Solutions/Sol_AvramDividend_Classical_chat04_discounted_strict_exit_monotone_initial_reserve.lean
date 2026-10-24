-- Prove2me | solution 1 for AvramDividend.Classical.chat04_discounted_strict_exit_monotone_initial_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:08:41.624773+00:00
-- url     : https://prove2.me/submissions/1dd473e1-4d9a-4f98-9866-6e0971d7d310

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_clocks_monotone_initial_reserve
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Raising initial reserve increases the strict killed upper-exit discount transform. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a x y : ℝ)
    (hq : 0 ≤ q) (hxy : x ≤ y) :
    twoSidedExitExpectation X q a x ≤ twoSidedExitExpectation X q a y := by
  unfold twoSidedExitExpectation
  apply lintegral_mono
  intro ω
  obtain ⟨hup, hdown⟩ :=
    chat04_strict_exit_clocks_monotone_initial_reserve X a x y hxy ω
  change
    (if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
      ENNReal.ofReal (Real.exp
        (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
     else 0) ≤
    (if twoSidedExitUpTime X (a - y) ω < twoSidedExitDownTime X (-y) ω then
      ENNReal.ofReal (Real.exp
        (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - y) ω))))
     else 0)
  by_cases hx : twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω
  · have hy : twoSidedExitUpTime X (a - y) ω <
        twoSidedExitDownTime X (-y) ω :=
      lt_of_le_of_lt hup (lt_of_lt_of_le hx hdown)
    simp only [if_pos hx, if_pos hy]
    have hxTop : twoSidedExitUpTime X (a - x) ω ≠ ⊤ :=
      ne_top_of_lt hx
    have hreal : ENNReal.toReal (twoSidedExitUpTime X (a - y) ω) ≤
        ENNReal.toReal (twoSidedExitUpTime X (a - x) ω) :=
      ENNReal.toReal_mono hxTop hup
    have hmul := mul_le_mul_of_nonneg_left hreal hq
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hmul))
  · simp only [if_neg hx]
    exact bot_le
