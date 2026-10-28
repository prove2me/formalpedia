-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_stopped_exit_payoff_pointwise_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:42:11.364455+00:00
-- url     : https://prove2.me/submissions/0adbe43a-fab7-48e2-bab3-19d35680856c

import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_payoff
import Theorems.Thm_AvramDividend_Classical_chat03_discounted_upperfirst_weight_le_one
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The successful strict upper-exit q-scale terminal payoff is bounded
pointwise by the scale value at the upper barrier whenever q is nonnegative. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (a x : ℝ) (hxa : x ≤ a)
    (W : ℝ → ℝ) (ω : Ω) :
    (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
     else 0) ≤ ENNReal.ofReal (W a) := by
  have hd :=
    chat03_discounted_upperfirst_weight_le_one
      q hq (twoSidedExitUpTime X (a - x) ω)
        (twoSidedExitDownTime X (-x) ω)
  calc
    _ = (if twoSidedExitUpTime X (a - x) ω <
             twoSidedExitDownTime X (-x) ω then
           ENNReal.ofReal (Real.exp
             (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
         else 0) * ENNReal.ofReal (W a) := by
      simpa only [ite_mul, zero_mul] using
        (chat04_strict_upper_exit_scale_payoff X W q a x hxa ω)
    _ ≤ (1 : ℝ≥0∞) * ENNReal.ofReal (W a) :=
      mul_le_mul_of_nonneg_right hd (by exact bot_le)
    _ = ENNReal.ofReal (W a) := one_mul _
