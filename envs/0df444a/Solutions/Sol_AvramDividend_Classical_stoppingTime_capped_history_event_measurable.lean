-- Prove2me | solution 1 for AvramDividend.Classical.stoppingTime_capped_history_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:34:51.0254+00:00
-- url     : https://prove2.me/submissions/ea45a5bc-ac3e-48bb-9d99-800145242b79

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0∞}
    (hτ : IsStoppingTime 𝓕 τ) (A : Set Ω)
    (hA : MeasurableSet[hτ.measurableSpace] A) (N : ℝ≥0) :
    MeasurableSet[(hτ.min_const N).measurableSpace]
      (A ∩ {ω : Ω | τ ω ≤ (N : ℝ≥0∞)}) := by
  rw [hτ.measurableSet_min_const_iff]
  constructor
  · exact hA.inter (hτ.measurableSet_le' N)
  · exact ((hτ.measurableSet A).mp hA).2 N
