-- Prove2me | solution 2 for AvramDividend.Classical.reflectedPath_dividendMeasure_zero_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:17:23.419679+00:00
-- url     : https://prove2.me/submissions/2a1360a5-a0c4-4282-aa09-6dc3d57998a0

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_of_right_continuous
import Theorems.Thm_AvramDividend_Classical_rightLim_comp_toNNReal_of_rightContinuous
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Iic_zero_of_monotone_rightLim

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (f M : ℝ≥0 → ℝ)
    (hM : Monotone M) (hdom : ∀ t, f t ≤ M t)
    (hrepr : ∀ t, M t =
      ⨆ s : Set.Icc (0 : ℝ≥0) t, f s.1)
    (hfRight : ∀ t, Tendsto f (𝓝[≥] t) (𝓝 (f t)))
    (ω : Ω) :
    dividendMeasure (fun t (_ : Ω) => M t) ω
      (Set.Iic (0 : ℝ)) = 0 := by
  refine AvramDividend.Classical.dividendMeasure_Iic_zero_of_monotone_rightLim _ ω
    (hM.comp fun _ _ h => Real.toNNReal_le_toNNReal h) fun r => ?_
  exact AvramDividend.Classical.rightLim_comp_toNNReal_of_rightContinuous M
    (AvramDividend.Classical.runningSup_right_continuous_of_right_continuous f M hM hdom hrepr hfRight) r
