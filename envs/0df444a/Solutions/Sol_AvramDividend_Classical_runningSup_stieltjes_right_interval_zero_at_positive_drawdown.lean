-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_stieltjes_right_interval_zero_at_positive_drawdown
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:48:03.704482+00:00
-- url     : https://prove2.me/submissions/95ed89e0-600c-46be-900f-30ff412a9d92

import Theorems.Thm_AvramDividend_Classical_runningSup_right_local_const_of_positive_drawdown
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment
import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.Order.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (u : ℝ≥0)
    (hPositive : 0 < reflectedSup X u ω) :
    ∃ v : ℝ≥0, u < v ∧
      (dividendMeasure (runningSup X) ω)
        (Set.Ioc (u : ℝ) (v : ℝ)) = 0 := by
  obtain ⟨v, huv, hv⟩ :=
    AvramDividend.Classical.runningSup_right_local_const_of_positive_drawdown X ω u hPositive
  obtain ⟨w, huw, hwv⟩ := exists_between huv
  refine ⟨w, huw, ?_⟩
  rw [AvramDividend.Classical.runningSup_dividendMeasure_Ioc_eq_record_increment,
    Real.toNNReal_coe, Real.toNNReal_coe, hv w huw.le hwv, sub_self, ENNReal.ofReal_zero]
