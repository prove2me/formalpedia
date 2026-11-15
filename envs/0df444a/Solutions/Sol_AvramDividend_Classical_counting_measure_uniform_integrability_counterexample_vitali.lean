-- Prove2me | solution 1 for AvramDividend.Classical.counting_measure_uniform_integrability_counterexample_vitali
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:36:52.666223+00:00
-- url     : https://prove2.me/submissions/376bce55-06ad-4831-baf1-9fd7e31d873d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_counting_delta_indicator_mean_and_pointwise_zero
import Theorems.Thm_AvramDividend_Classical_counting_delta_unif_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped NNReal ENNReal
noncomputable section
theorem solution :
    ∃ Y : ℕ → ℕ → ℝ,
      UniformIntegrable Y 1 (Measure.count : Measure ℕ) ∧
      (∀ ω : ℕ, Tendsto (fun n => Y n ω) atTop (nhds 0)) ∧
      (∀ n : ℕ, (∫ ω, Y n ω ∂(Measure.count : Measure ℕ)) = 1) := by
  let Y : ℕ → ℕ → ℝ := fun n => ({n} : Set ℕ).indicator (fun _ => 1)
  have hm := AvramDividend.Classical.counting_delta_indicator_mean_and_pointwise_zero
  have hu := AvramDividend.Classical.counting_delta_unif_integrable
  refine ⟨Y, ?_, hm.2, hm.1⟩
  refine ⟨?_, hu, ⟨1, ?_⟩⟩
  · intro n
    exact (measurable_const.indicator (measurableSet_singleton n)).aestronglyMeasurable
  · intro n
    change eLpNorm (({n} : Set ℕ).indicator (fun _ => (1 : ℝ))) 1
      (Measure.count : Measure ℕ) ≤ (1 : ℝ≥0)
    rw [eLpNorm_indicator_const (measurableSet_singleton n) (by norm_num) (by norm_num)]
    simp
