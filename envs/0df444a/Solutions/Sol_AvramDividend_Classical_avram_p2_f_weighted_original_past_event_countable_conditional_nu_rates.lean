-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_past_event_countable_conditional_nu_rates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:46:37.093887+00:00
-- url     : https://prove2.me/submissions/dea99d08-a256-499d-837a-7813e18cd432

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_past_event_origin_means

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original actual-process countable past-event
compensation with independent zero-origin ν-rate identification explicit. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ι → ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet[𝓕 (s i)] (A i))
    (hOrigin : ∀ i, (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 (T i) ×ˢ B i) ∂P) = (((T i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))) :
    (∫⁻ ω, ∑' i, (A i).indicator (fun ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc (s i) (s i + T i) ×ˢ B i)) ω ∂P) =
    ∑' i, P (A i) * (((T i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by
  calc
    (∫⁻ ω, ∑' i, (A i).indicator (fun ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc (s i) (s i + T i) ×ˢ B i)) ω ∂P) =
    ∑' i, P (A i) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 (T i) ×ˢ B i) ∂P) := avram_p2_f_weighted_original_countable_past_event_origin_means
      X s T B hB A hA
    _ = ∑' i, P (A i) * (((T i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by
      congr 1
      funext i
      rw [hOrigin i]
