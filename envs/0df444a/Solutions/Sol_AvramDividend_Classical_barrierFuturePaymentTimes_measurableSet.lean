-- Prove2me | solution 1 for AvramDividend.Classical.barrierFuturePaymentTimes_measurableSet
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:13:50.657214+00:00
-- url     : https://prove2.me/submissions/e264f3d5-6a48-4a5a-9398-d33ad6f0d771

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution (σ : ℝ≥0∞) :
    MeasurableSet (paymentTimes σ) := by
  have : paymentTimes σ = {t : ℝ | 0 ≤ t} ∩ ({0} ∪ {t | ENNReal.ofReal t < σ}) := by
    ext t; simp [paymentTimes]
  rw [this]
  exact (measurableSet_le measurable_const measurable_id).inter
    ((measurableSet_singleton 0).union (measurableSet_lt ENNReal.measurable_ofReal measurable_const))
