-- Prove2me | solution 1 for AvramDividend.Classical.reflectedPath_dividendMeasure_zero_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:16:49.073715+00:00
-- url     : https://prove2.me/submissions/d60166fa-7712-4f4b-b2e2-bbc062727149

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_of_right_continuous
import Theorems.Thm_AvramDividend_Classical_rightLim_comp_toNNReal_of_rightContinuous
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Iic_zero_of_monotone_rightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
  have hm : Monotone
      (fun r : ℝ => M r.toNNReal) :=
    hM.comp Real.toNNReal_monotone
  have hcont : ∀ t : ℝ≥0,
      ContinuousWithinAt M (Set.Ici t) t := by
    intro t
    exact runningSup_right_continuous_of_right_continuous
      f M hM hdom hrepr hfRight t
  have hr : ∀ r : ℝ,
      Function.rightLim (fun s : ℝ => M s.toNNReal) r =
        M r.toNNReal :=
    rightLim_comp_toNNReal_of_rightContinuous M hcont
  exact dividendMeasure_Iic_zero_of_monotone_rightLim
    (fun t (_ : Ω) => M t) ω hm hr
