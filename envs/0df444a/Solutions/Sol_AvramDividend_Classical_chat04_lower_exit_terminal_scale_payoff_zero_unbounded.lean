-- Prove2me | solution 1 for AvramDividend.Classical.chat04_lower_exit_terminal_scale_payoff_zero_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:26:07.735979+00:00
-- url     : https://prove2.me/submissions/487e4e16-e154-4d2c-90af-5be7c0490239

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_scale_terminal_payoff_zero_of_Wzero
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- In the unbounded-variation regime, the q-scale payoff at a
strict lower-ruin exit is zero on every sample path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ω : Ω) :
    (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0) = 0 := by
  exact chat04_lower_exit_scale_terminal_payoff_zero_of_Wzero
    X q W hW
    (chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW)
    a x ω
