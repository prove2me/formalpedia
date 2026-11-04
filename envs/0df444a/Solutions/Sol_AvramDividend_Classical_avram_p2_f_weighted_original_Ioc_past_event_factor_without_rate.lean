-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_Ioc_past_event_factor_without_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:02:47.383274+00:00
-- url     : https://prove2.me/submissions/c8cff9d3-cb47-4ecf-a188-141b5398bb22

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_Ioc_st_future_past_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original predictable-event restriction of the genuine marked count factors
at its past time; independent of ν, separated marks and finite moments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc s t ×ˢ B) ∂P) =
    P A * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc s t ×ˢ B) ∂P) := by
  let N : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc s t ×ˢ B)
  let H : Ω → ℝ≥0∞ := A.indicator (fun _ => 1)
  have hAamb : MeasurableSet A := (𝓕.le s) _ hA
  have hH : Measurable[𝓕 s] H := by
    exact (measurable_const : Measurable[𝓕 s] (fun _ : Ω => (1 : ℝ≥0∞))).indicator hA
  have hPointwise (ω : Ω) : H ω * N ω = (A.indicator N) ω := by
    by_cases hω : ω ∈ A <;> simp [H, Set.indicator, hω]
  change (∫⁻ ω in A, N ω ∂P) = P A * (∫⁻ ω, N ω ∂P)
  calc
    (∫⁻ ω in A, N ω ∂P) =
        (∫⁻ ω, (A.indicator N) ω ∂P) := by
      exact (lintegral_indicator hAamb N).symm
    _ = (∫⁻ ω, H ω * N ω ∂P) := by
      congr 1
      funext ω
      exact (hPointwise ω).symm
    _ = (∫⁻ ω, H ω ∂P) * (∫⁻ ω, N ω ∂P) := by
      exact avram_p2_f_weighted_original_intrinsic_Ioc_st_future_past_factor
        X s t hst B hB H hH
    _ = P A * (∫⁻ ω, N ω ∂P) := by
      rw [show (∫⁻ ω, H ω ∂P) = P A from lintegral_indicator_one hAamb]
