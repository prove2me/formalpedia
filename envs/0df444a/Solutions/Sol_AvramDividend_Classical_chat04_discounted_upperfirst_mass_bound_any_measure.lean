-- Prove2me | solution 1 for AvramDividend.Classical.chat04_discounted_upperfirst_mass_bound_any_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:19:59.469438+00:00
-- url     : https://prove2.me/submissions/d4704f62-d5df-4b08-9b4c-7a4f8936901b

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_lower_passage_event_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Nonnegative-discount killed upper-first reward is bounded by event mass under any law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (q a x : ℝ) (hq : 0 ≤ q) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) ≤
    μ {ω : Ω | twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω} := by
  have hEvent : MeasurableSet
      {ω : Ω | twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω} :=
    chat03_upper_before_lower_passage_event_measurable X (-x) (a - x)
  calc
    (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
            (twoSidedExitUpTime X (a - x) ω)))) else 0 ∂μ) ≤
        (∫⁻ ω, ({ω : Ω | twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω}).indicator
          (fun _ => (1 : ℝ≥0∞)) ω ∂μ) := by
      apply lintegral_mono
      intro ω
      simp only [Set.indicator, Set.mem_setOf_eq]
      by_cases h : twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω
      · simp only [if_pos h]
        have hmul : 0 ≤ q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω) :=
          mul_nonneg hq ENNReal.toReal_nonneg
        have hexp : Real.exp (-(q * ENNReal.toReal
            (twoSidedExitUpTime X (a - x) ω))) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr hmul)
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hexp
      · simp [h]
    _ = μ {ω : Ω | twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω} := by
      simpa [Set.indicator] using
        (MeasureTheory.lintegral_indicator_one (μ := μ) hEvent)
