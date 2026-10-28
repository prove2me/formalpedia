-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_stopped_scale_negative_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T00:32:21.443909+00:00
-- url     : https://prove2.me/submissions/867de821-cedb-4d0a-b463-d6693e854cc7

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_exit_terminal_payoff_factorisation_unbounded
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_discount_zero_of_negative_reserve
import Mathlib.Analysis.Complex.Exponential

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
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (hxa : x ≤ a) (hx : x < 0) :
    (∫⁻ ω, (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0) + (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
      else 0) ∂P) = ENNReal.ofReal (W x) := by
  classical
  have hWx : W x = 0 := hW.1 x hx
  have hExit : twoSidedExitExpectation X q a x = 0 :=
    chat04_strict_exit_discount_zero_of_negative_reserve X q a x hx
  calc
    _ = twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) :=
      chat04_strict_two_sided_exit_terminal_payoff_factorisation_unbounded
        X hnbv q hq W hW a x hxa
    _ = ENNReal.ofReal (W x) := by simp [hWx, hExit]
