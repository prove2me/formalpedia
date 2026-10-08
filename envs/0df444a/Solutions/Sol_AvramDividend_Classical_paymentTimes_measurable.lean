-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:39:42.632247+00:00
-- url     : https://prove2.me/submissions/ddfa43ce-fdec-4d73-8fa1-d0336a9b59b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution (σ : ℝ≥0∞) :
    MeasurableSet (paymentTimes σ) := by
  have hOpen : IsOpen {t : ℝ | ENNReal.ofReal t < σ} := by
    exact isOpen_Iio.preimage ENNReal.continuous_ofReal
  change MeasurableSet
    (Ici (0 : ℝ) ∩ ({0} ∪ {t : ℝ | ENNReal.ofReal t < σ}))
  exact measurableSet_Ici.inter
    (measurableSet_singleton (0 : ℝ) |>.union hOpen.measurableSet)
