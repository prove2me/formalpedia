-- Prove2me | solution 1 for AvramDividend.Classical.capped_stopping_terminal_integrable_of_continuous_paths
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T10:34:29.885993+00:00
-- url     : https://prove2.me/submissions/f8d9a492-98fd-4fad-b1c4-b1113b08daa6

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_progMeasurable_of_continuous_paths
import Theorems.Thm_AvramDividend_Classical_capped_stopping_terminal_integrable_from_progressive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Continuous adapted paths remove the separate progressivity assumption at stopping horizons. -/
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
    (hXCont : ∀ ω, Continuous (fun t => X.X t ω))
    (hDCont : ∀ ω, Continuous (fun t => D t ω)) :
    Integrable (fun ω => if ((τ ω : ℝ≥0) : ℝ≥0∞) <
      ruinTime X x D ω then
      w (riskProcess X x D (τ ω) ω) else 0) P := by
  have hProg : ProgMeasurable 𝓕 (riskProcess X x D) :=
    riskProcess_progMeasurable_of_continuous_paths
      X x D hD.1.1 hXCont hDCont
  exact capped_stopping_terminal_integrable_from_progressive
    X w hw B hB x hx hxc D hD τ hStop hProg
