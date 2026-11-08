-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_turn10_positive_event_condexp_martingale_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T23:57:17.738526+00:00
-- url     : https://prove2.me/submissions/4b21eab2-9058-4d34-9e24-8fccb401f4b3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gaussian11_strict_positive_stopping_clock_condexp_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An integrable positive-clock payoff dominated by its benchmark plus a
conditionally centred martingale has the probability-weighted upper bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (b : ℝ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (F M : Ω → ℝ) (hFI : Integrable F P) (hMI : Integrable M P)
    (hCondZero : ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P M ω = 0)
    (hUpper : ∀ ω, F ω ≤ b + M ω) :
    (∫ ω in {ω : Ω | σ ω ≠ 0}, F ω ∂P) ≤
      b * (P {ω : Ω | σ ω ≠ 0}).toReal := by
  let B : Set Ω := {ω : Ω | σ ω ≠ 0}
  have hB : MeasurableSet B :=
    (avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
      𝓕 σ hσstop).compl
  have hMzero : (∫ ω in B, M ω ∂P) = 0 :=
    avram_gaussian11_strict_positive_stopping_clock_condexp_zero
      σ hσstop M hMI hCondZero
  have hAddI : Integrable (fun ω => b + M ω) P :=
    (integrable_const b).add hMI
  have hLe : (∫ ω in B, F ω ∂P) ≤
      ∫ ω in B, b + M ω ∂P :=
    setIntegral_mono_on hFI.integrableOn hAddI.integrableOn hB
      (by intro ω _; exact hUpper ω)
  calc
    (∫ ω in B, F ω ∂P) ≤ ∫ ω in B, b + M ω ∂P := hLe
    _ = (∫ _ in B, b ∂P) + (∫ ω in B, M ω ∂P) := by
      exact integral_add (integrable_const b).integrableOn hMI.integrableOn
    _ = b * (P B).toReal := by
      rw [hMzero, add_zero, setIntegral_const]
      simp [smul_eq_mul, Measure.real, mul_comm]
