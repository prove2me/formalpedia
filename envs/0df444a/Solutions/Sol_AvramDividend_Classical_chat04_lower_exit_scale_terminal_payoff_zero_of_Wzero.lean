-- Prove2me | solution 1 for AvramDividend.Classical.chat04_lower_exit_scale_terminal_payoff_zero_of_Wzero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:07:58.12899+00:00
-- url     : https://prove2.me/submissions/6ebf0e09-4556-45ee-8bb6-1a4c9a5cbf0f

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_scale_creeping_atom
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- The strict ruin-before-upper-exit terminal scale payoff vanishes
pathwise when the q-scale function vanishes at the origin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hWzero : W 0 = 0)
    (a x : ℝ) (ω : Ω) :
    (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0) = 0 := by
  rw [chat04_lower_exit_scale_creeping_atom X q W hW a x ω]
  simp [hWzero]
