-- Prove2me | solution 2 for AvramDividend.Classical.stoppingTime_capped_history_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:34:59.49147+00:00
-- url     : https://prove2.me/submissions/1dcbef79-b038-454f-8c39-02bdb283a196

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0∞}
    (hτ : IsStoppingTime 𝓕 τ) (A : Set Ω)
    (hA : MeasurableSet[hτ.measurableSpace] A) (N : ℝ≥0) :
    MeasurableSet[(hτ.min_const N).measurableSpace]
      (A ∩ {ω : Ω | τ ω ≤ (N : ℝ≥0∞)}) := by 
  exact (IsStoppingTime.measurableSet_inter_le_const_iff hτ _ N).1 (hA.inter (hτ.measurableSet_le' N))
