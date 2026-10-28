-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_stopped_scale_zero_reserve_of_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:56:05.276008+00:00
-- url     : https://prove2.me/submissions/59196a85-4221-4663-bf44-2eec968dc119

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_exit_terminal_payoff_factorisation_unbounded
import Theorems.Thm_AvramDividend_Classical_chat04_zero_start_two_sided_exit_expectation_of_near_zero
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hnear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0) :
    (∫⁻ ω, (if twoSidedExitUpTime X a ω <
          twoSidedExitDownTime X 0 ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X a ω)))) *
          ENNReal.ofReal
            (W (X.X (twoSidedExitUpTime X a ω).toNNReal ω))
      else 0) + (if twoSidedExitDownTime X 0 ω <
          twoSidedExitUpTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X 0 ω)))) *
          ENNReal.ofReal
            (W (X.X (twoSidedExitDownTime X 0 ω).toNNReal ω))
      else 0) ∂P) = ENNReal.ofReal (W 0) := by
  have hfactor :=
    chat04_strict_two_sided_exit_terminal_payoff_factorisation_unbounded
      X hnbv q hq W hW a 0 (le_of_lt ha)
  have hExitZero :
      twoSidedExitExpectation X q a 0 = 0 :=
    chat04_zero_start_two_sided_exit_expectation_of_near_zero X q a hnear
  have hWzero : W 0 = 0 :=
    chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW
  simpa [hExitZero, hWzero] using hfactor
