-- Prove2me | solution 1 for AvramDividend.Classical.stoppingTime_finite_cap_untopA_le_events
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:33:49.66798+00:00
-- url     : https://prove2.me/submissions/be4de29e-94fe-44af-80bf-d88c44ea3ff2

import Mathlib.Probability.Process.Stopping
import Mathlib.Order.WithBot

open MeasureTheory
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0∞}
    (hτ : IsStoppingTime 𝓕 τ) (N : ℝ≥0) :
    ∀ s : ℝ≥0, MeasurableSet[𝓕 s]
      {ω : Ω | (min (τ ω) (N : ℝ≥0∞)).untopA ≤ s} := by 
  intro s
  have hset : {ω : Ω | (min (τ ω) (N : ℝ≥0∞)).untopA ≤ s} =
      {ω | τ ω ≤ (s : ℝ≥0∞)} ∪ {_ω | (N : ℝ≥0∞) ≤ s} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union]
    rw [WithTop.untopA_le_iff (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))]
    exact (min_le_iff (a := (s : ℝ≥0∞)) (b := τ ω) (c := (N : ℝ≥0∞)))
  rw [hset]
  exact (hτ.measurableSet_le s).union (MeasurableSet.const _)
