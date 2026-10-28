-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_stopped_scale_upper_endpoint_of_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:59:18.21403+00:00
-- url     : https://prove2.me/submissions/78844802-fc5b-4546-bd43-00d38907e161

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_strict_two_sided_exit_terminal_payoff_factorisation_unbounded
import Theorems.Thm_AvramDividend_Classical_chat04_upper_endpoint_exit_expectation_of_ae_upward_regularity
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
    (hplus : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ 0 < X.X t ω) :
    (∫⁻ ω, (if twoSidedExitUpTime X 0 ω <
          twoSidedExitDownTime X (-a) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X 0 ω)))) *
          ENNReal.ofReal
            (W (a + X.X (twoSidedExitUpTime X 0 ω).toNNReal ω))
      else 0) + (if twoSidedExitDownTime X (-a) ω <
          twoSidedExitUpTime X 0 ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-a) ω)))) *
          ENNReal.ofReal
            (W (a + X.X (twoSidedExitDownTime X (-a) ω).toNNReal ω))
      else 0) ∂P) = ENNReal.ofReal (W a) := by
  have hfactor :=
    chat04_strict_two_sided_exit_terminal_payoff_factorisation_unbounded
      X hnbv q hq W hW a a le_rfl
  have hExitOne :
      twoSidedExitExpectation X q a a = 1 :=
    chat04_upper_endpoint_exit_expectation_of_ae_upward_regularity
      X q a ha hplus
  simpa [hExitOne] using hfactor
