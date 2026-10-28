-- Prove2me | solution 1 for AvramDividend.Classical.localized_stopped_terminal_lintegral_iSup_bands
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:42:29.310334+00:00
-- url     : https://prove2.me/submissions/1af84b43-bb43-4405-9868-046bd530d96a

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_survival_event_measurable_of_stopping_and_admissible
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
import Theorems.Thm_AvramDividend_Classical_localized_nonnegative_terminal_lintegral_iSup_bands

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- At a stopped reserve the nonnegative terminal value is exhausted by finite bands. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ)
    (hProg : ProgMeasurable 𝓕 (riskProcess X x D)) :
    (∫⁻ ω, if τ ω < ruinTime X x D ω ∧
        0 ≤ stoppedValue (riskProcess X x D) τ ω then
        ENNReal.ofReal (w (stoppedValue (riskProcess X x D) τ ω))
      else 0 ∂P) =
    ⨆ n : ℕ, (∫⁻ ω, if τ ω < ruinTime X x D ω ∧
        0 ≤ stoppedValue (riskProcess X x D) τ ω ∧
        stoppedValue (riskProcess X x D) τ ω ≤ (n : ℝ) then
        ENNReal.ofReal (w (stoppedValue (riskProcess X x D) τ ω))
      else 0 ∂P) := by
  let A : Set Ω := {ω | τ ω < ruinTime X x D ω}
  have hA : MeasurableSet A :=
    survival_event_measurable_of_stopping_and_admissible X x D hD τ hτ
  have hReserve : Measurable (stoppedValue (riskProcess X x D) τ) :=
    (measurable_stoppedValue hProg hτ).mono hτ.measurableSpace_le le_rfl
  have hwMeas : Measurable w :=
    (local_verification_candidate_borel_and_postPayment_adapted
      X x D hD w hw hw_neg).1
  simpa only [A, Set.mem_setOf_eq] using
    (localized_nonnegative_terminal_lintegral_iSup_bands
      P A hA (stoppedValue (riskProcess X x D) τ) hReserve w hwMeas)
