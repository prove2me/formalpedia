-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_countable_past_event_origin_means
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:29:36.861181+00:00
-- url     : https://prove2.me/submissions/c1308aed-65af-4028-a55e-df83fdb693de

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_predictable_origin_means

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Countably many genuine original future marked counts restricted to
individually adapted past events factor into event probabilities and source
zero-origin expected counts, with ENNReal zero-times-infinity behaviour. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ι → ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (A : ι → Set Ω) (hA : ∀ i, MeasurableSet[𝓕 (s i)] (A i)) :
    (∫⁻ ω, ∑' i, (A i).indicator (fun ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc (s i) (s i + T i) ×ˢ B i)) ω ∂P) =
    ∑' i, P (A i) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 (T i) ×ˢ B i) ∂P) := by
  let H : ι → Ω → ℝ≥0∞ := fun i => (A i).indicator (fun _ => 1)
  have hH (i : ι) : Measurable[𝓕 (s i)] (H i) := by
    exact (measurable_const : Measurable[𝓕 (s i)]
      (fun _ : Ω => (1 : ℝ≥0∞))).indicator (hA i)
  have hPoint (i : ι) (ω : Ω) :
      (A i).indicator (fun ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc (s i) (s i + T i) ×ˢ B i)) ω =
      H i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc (s i) (s i + T i) ×ˢ B i) := by
    by_cases hi : ω ∈ A i <;> simp [H, Set.indicator, hi]
  have hMean (i : ι) : (∫⁻ ω, H i ω ∂P) = P (A i) := by
    have hAmbient : MeasurableSet (A i) := (𝓕.le (s i)) _ (hA i)
    exact lintegral_indicator_one hAmbient
  calc
    (∫⁻ ω, ∑' i, (A i).indicator (fun ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc (s i) (s i + T i) ×ˢ B i)) ω ∂P) =
        (∫⁻ ω, ∑' i, H i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc (s i) (s i + T i) ×ˢ B i) ∂P) := by
          congr 1
          funext ω
          congr 1
          funext i
          exact hPoint i ω
    _ = ∑' i, (∫⁻ ω, H i ω ∂P) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 (T i) ×ˢ B i) ∂P) :=
      avram_p2_f_weighted_original_countable_predictable_origin_means
        X s T B hB H hH
    _ = ∑' i, P (A i) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 (T i) ×ˢ B i) ∂P) := by
      congr 1
      funext i
      rw [hMean i]
