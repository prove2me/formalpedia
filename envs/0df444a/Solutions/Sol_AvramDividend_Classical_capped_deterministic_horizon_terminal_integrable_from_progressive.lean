-- Prove2me | solution 1 for AvramDividend.Classical.capped_deterministic_horizon_terminal_integrable_from_progressive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:08:33.772984+00:00
-- url     : https://prove2.me/submissions/dbf16c45-a451-4671-91b3-6c82b9abe2ee

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_stopping_terminal_integrable_from_progressive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A fixed-horizon capped terminal HJB payoff is integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (B : ℝ) (hB : 0 ≤ B)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal B)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x (ENNReal.ofReal B) D)
    (T : ℝ≥0)
    (hProg : ProgMeasurable 𝓕 (riskProcess X x D)) :
    Integrable (fun ω => if (T : ℝ≥0∞) < ruinTime X x D ω then
      w (riskProcess X x D T ω) else 0) P := by
  have hStop : IsStoppingTime 𝓕 (fun _ : Ω => (T : ℝ≥0∞)) :=
    isStoppingTime_const 𝓕 T
  exact capped_stopping_terminal_integrable_from_progressive
    X w hw B hB x hx hxc D hD (fun _ => T) hStop hProg
