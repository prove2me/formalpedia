-- Prove2me | solution 1 for AvramDividend.Classical.capped_stopping_terminal_integrable_from_progressive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:03:42.090988+00:00
-- url     : https://prove2.me/submissions/6cdb5134-8b89-4f6b-91ce-51d2cf5b66ec

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_surviving_stoppedValue_range_real
import Theorems.Thm_AvramDividend_Classical_capped_survival_stopped_test_aestronglyMeasurable_of_continuousOn
import Theorems.Thm_AvramDividend_Classical_capped_surviving_terminal_test_integrable_of_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Integrability of a capped stopped HJB payoff under progressive measurability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (B : ℝ) (hB : 0 ≤ B)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal B)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x (ENNReal.ofReal B) D)
    (τ : Ω → ℝ≥0)
    (hStop : IsStoppingTime 𝓕 (fun ω => ((τ ω : ℝ≥0) : ℝ≥0∞)))
    (hProg : ProgMeasurable 𝓕 (riskProcess X x D)) :
    Integrable (fun ω => if ((τ ω : ℝ≥0) : ℝ≥0∞) <
      ruinTime X x D ω then
      w (riskProcess X x D (τ ω) ω) else 0) P := by
  have hwCompact : ContinuousOn w (Icc (0 : ℝ) B) :=
    hw.mono (by intro y hy; exact hy.1)
  have hCap : ∀ ω,
      ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω →
      stoppedValue (riskProcess X x D)
        (fun ω => ((τ ω : ℝ≥0) : ℝ≥0∞)) ω ∈ Icc (0 : ℝ) B := by
    intro ω hSurvive
    exact capped_surviving_stoppedValue_range_real
      X x B hx hB (ENNReal.ofReal B) rfl hxc D hD
      (fun ω => ((τ ω : ℝ≥0) : ℝ≥0∞)) ω hSurvive
  have hMeasStopped :=
    capped_survival_stopped_test_aestronglyMeasurable_of_continuousOn
      X w B hwCompact x D hD.1.1
      (fun ω => ((τ ω : ℝ≥0) : ℝ≥0∞)) hStop hProg hCap
  have hTime (ω : Ω) :
      WithTop.untopA (((τ ω : ℝ≥0) : ℝ≥0∞)) = τ ω := by
    exact WithTop.untopD_coe (Classical.arbitrary ℝ≥0) (τ ω)
  have hMeas : AEStronglyMeasurable
      (fun ω => if ((τ ω : ℝ≥0) : ℝ≥0∞) <
        ruinTime X x D ω then
        w (riskProcess X x D (τ ω) ω) else 0) P := by
    simpa only [stoppedValue, hTime] using hMeasStopped
  exact capped_surviving_terminal_test_integrable_of_measurable
    X w hw B hB x hx hxc D hD τ hMeas
