-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_stopped_scale_nonpositive_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T00:28:40.363439+00:00
-- url     : https://prove2.me/submissions/7bb62c0b-f966-4e94-b4dc-fd562b01d94e

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_exit_terminal_payoff_factorisation_unbounded
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
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
    (a x : ℝ) (hxa : x ≤ a) (ha : a ≤ 0) :
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
  have hzero : W 0 = 0 :=
    chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW
  have hWa : W a = 0 := by
    rcases lt_or_eq_of_le ha with haneg | ha0
    · exact hW.1 a haneg
    · rw [ha0]
      exact hzero
  have hWx : W x = 0 := by
    have hx0 : x ≤ 0 := le_trans hxa ha
    rcases lt_or_eq_of_le hx0 with hxneg | hxzero
    · exact hW.1 x hxneg
    · rw [hxzero]
      exact hzero
  calc
    _ = twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) :=
      chat04_strict_two_sided_exit_terminal_payoff_factorisation_unbounded
        X hnbv q hq W hW a x hxa
    _ = ENNReal.ofReal (W x) := by simp [hWa, hWx]
