-- Prove2me | solution 1 for AvramDividend.Classical.chat04_two_grid_survival_past_condExp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T07:15:36.431738+00:00
-- url     : https://prove2.me/submissions/8aa34773-2076-484f-82af-9fcb2340518a

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_standing_past_event_scale_condExp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Conditional q-scale expectation on the explicit two-observation historical
survival event. The event is F_t-measurable by adaptedness and filtration
monotonicity. Integrability follows automatically from Standing.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u)
    (x : ℝ) :
    P[({ω | 0 ≤ x + X.X s ω ∧ 0 ≤ x + X.X t ω}).indicator
        (fun ω => W (x + (X.X u ω - X.X t ω))) | 𝓕 t] =ᵐ[P]
      ({ω | 0 ≤ x + X.X s ω ∧ 0 ≤ x + X.X t ω}).indicator
        (fun _ => ∫ ω, W (x + X.X (u - t) ω) ∂P) := by
  have hXs : Measurable[𝓕 t] (X.X s) :=
    (X.adapted s).mono (𝓕.mono hst) le_rfl
  have hXt : Measurable[𝓕 t] (X.X t) := X.adapted t
  have hLeft :
      MeasurableSet[𝓕 t] {ω | 0 ≤ x + X.X s ω} := by
    change MeasurableSet[𝓕 t]
      ((fun ω => x + X.X s ω) ⁻¹' Set.Ici (0 : ℝ))
    exact isClosed_Ici.measurableSet.preimage (measurable_const.add hXs)
  have hRight :
      MeasurableSet[𝓕 t] {ω | 0 ≤ x + X.X t ω} := by
    change MeasurableSet[𝓕 t]
      ((fun ω => x + X.X t ω) ⁻¹' Set.Ici (0 : ℝ))
    exact isClosed_Ici.measurableSet.preimage (measurable_const.add hXt)
  have hSurvival :
      MeasurableSet[𝓕 t]
        {ω | 0 ≤ x + X.X s ω ∧ 0 ≤ x + X.X t ω} := by
    exact hLeft.inter hRight
  exact AvramDividend.Classical.chat04_standing_past_event_scale_condExp
    X hX q hq W hW t u htu x
    {ω | 0 ≤ x + X.X s ω ∧ 0 ≤ x + X.X t ω} hSurvival
