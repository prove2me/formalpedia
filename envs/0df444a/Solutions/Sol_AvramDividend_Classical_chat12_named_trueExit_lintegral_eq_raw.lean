-- Prove2me | solution 1 for AvramDividend.Classical.chat12_named_trueExit_lintegral_eq_raw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:01:21.766423+00:00
-- url     : https://prove2.me/submissions/13cf9808-8bfb-43ad-a7d2-a888a9fd3063

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a ε : ℝ) :
    (∫⁻ ω, if twoSidedExitUpTime X ε ω <
        twoSidedExitDownTime X (ε - a) ω then
      ENNReal.ofReal (Real.exp
        (-(q * (twoSidedExitUpTime X ε ω).toReal)))
    else 0 ∂P) =
    (∫⁻ ω, if
      (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
      (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
      ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
    else 0 ∂P) := by
  apply lintegral_congr
  intro ω
  by_cases hω :
      (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
      (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞))
  · have hNamedEvent :
        twoSidedExitUpTime X ε ω <
          twoSidedExitDownTime X (ε - a) ω := by
      simpa only [twoSidedExitUpTime, twoSidedExitDownTime] using hω
    simp only [if_pos hNamedEvent, if_pos hω]
    rfl
  · have hNamedEvent :
        ¬ (twoSidedExitUpTime X ε ω <
          twoSidedExitDownTime X (ε - a) ω) := by
      simpa only [twoSidedExitUpTime, twoSidedExitDownTime] using hω
    simp only [if_neg hNamedEvent, if_neg hω]
