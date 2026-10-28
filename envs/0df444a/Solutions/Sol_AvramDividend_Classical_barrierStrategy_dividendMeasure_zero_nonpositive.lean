-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_dividendMeasure_zero_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:16:54.723995+00:00
-- url     : https://prove2.me/submissions/056a8906-bdc6-4802-b730-034a4e505afe

import Mathlib.Data.NNReal.Defs
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_below_barrier
import Theorems.Thm_AvramDividend_Classical_rightLim_comp_toNNReal_of_rightContinuous
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Iic_zero_of_monotone_rightLim
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) (ω : Ω) :
    dividendMeasure (barrierStrategy X x a) ω
      (Set.Iic (0 : ℝ)) = 0 := by
  have ha : 0 ≤ a := le_trans hx0 hxa
  have hD : IsDividendStrategy 𝓕 (barrierStrategy X x a) :=
    barrierStrategy_isDividendStrategy_nonnegative_barrier X x a hx0 ha
  have hm : Monotone
      (fun r : ℝ => barrierStrategy X x a r.toNNReal ω) :=
    (hD.2.1 ω).comp Real.toNNReal_monotone
  have hr : ∀ r : ℝ,
      Function.rightLim
        (fun s : ℝ => barrierStrategy X x a s.toNNReal ω) r =
          barrierStrategy X x a r.toNNReal ω :=
    rightLim_comp_toNNReal_of_rightContinuous
      (fun t : ℝ≥0 => barrierStrategy X x a t ω)
      (barrierStrategy_right_continuous_below_barrier X x a
        hx0 ha hxa ω)
  exact dividendMeasure_Iic_zero_of_monotone_rightLim
    (barrierStrategy X x a) ω hm hr
