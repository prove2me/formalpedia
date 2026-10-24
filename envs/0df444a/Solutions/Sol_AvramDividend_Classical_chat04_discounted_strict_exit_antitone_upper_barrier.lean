-- Prove2me | solution 1 for AvramDividend.Classical.chat04_discounted_strict_exit_antitone_upper_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:37:24.758637+00:00
-- url     : https://prove2.me/submissions/73fe74d1-e470-47b0-b9ae-4de55cc29244

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_success_antitone_upper_barrier
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-!
For nonnegative discount, a higher upper barrier decreases the killed
two-sided exit expectation. Strict upcrossing clocks and ruin priority
are preserved, including finite-time and infinity distinctions.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a b x : ℝ)
    (hq : 0 ≤ q) (hab : a ≤ b) :
    twoSidedExitExpectation X q b x ≤ twoSidedExitExpectation X q a x := by
  unfold twoSidedExitExpectation
  apply lintegral_mono
  intro ω
  obtain ⟨hup, hsuccess⟩ :=
    chat04_strict_exit_success_antitone_upper_barrier X a b x hab ω
  change
    (if twoSidedExitUpTime X (b - x) ω < twoSidedExitDownTime X (-x) ω then
      ENNReal.ofReal (Real.exp
        (-(q * ENNReal.toReal (twoSidedExitUpTime X (b - x) ω))))
     else 0) ≤
    (if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
      ENNReal.ofReal (Real.exp
        (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
     else 0)
  by_cases hb : twoSidedExitUpTime X (b - x) ω <
      twoSidedExitDownTime X (-x) ω
  · have ha : twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω := hsuccess hb
    simp only [if_pos hb, if_pos ha]
    have hbtop : twoSidedExitUpTime X (b - x) ω ≠ ⊤ :=
      ne_top_of_lt hb
    have hreal : ENNReal.toReal (twoSidedExitUpTime X (a - x) ω) ≤
        ENNReal.toReal (twoSidedExitUpTime X (b - x) ω) :=
      ENNReal.toReal_mono hbtop hup
    have hmul := mul_le_mul_of_nonneg_left hreal hq
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hmul))
  · simp only [if_neg hb]
    exact bot_le
