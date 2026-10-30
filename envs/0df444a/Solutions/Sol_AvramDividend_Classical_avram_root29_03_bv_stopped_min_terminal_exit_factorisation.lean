-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_bv_stopped_min_terminal_exit_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:38:09.579008+00:00
-- url     : https://prove2.me/submissions/07c9510c-cffc-450b-907c-433a2808d24e

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_exact_qscale_two_branch_terminal_conversion
import Theorems.Thm_AvramDividend_Classical_chat04_strict_upper_exit_scale_terminal_payoff_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_strict_stopped_exit_payoff_any_measure_factorisation
import Theorems.Thm_AvramDividend_Classical_bv_lower_exit_discounted_scale_payoff_zero_ws01c

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Under Standing and bounded variation, the genuine finite minimum
stopped discounted q-scale terminal payoff factors through the
strict upward-before-ruin discount expectation. The killed martingale
identity is a separate stochastic obligation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω, if min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω) < ⊤ then
      ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω))))) *
        ENNReal.ofReal
          (W (x + X.X (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal ω)) else 0 ∂P) =
    twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) := by
  have hSplit :=
    avram_root29_03_exact_qscale_two_branch_terminal_conversion
      X q W hW a x ha hxa
  have hUpper :
      Measurable (fun ω : Ω =>
        if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
          ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
        else 0) :=
    chat04_strict_upper_exit_scale_terminal_payoff_measurable
      X q a x hxa W
  rw [lintegral_add_left hUpper] at hSplit
  have hLower :=
    bv_lower_exit_discounted_scale_payoff_zero_ws01c
      X hX q hq W hW hBV a x ha hx0 hxa
  have hFactor :=
    chat04_strict_stopped_exit_payoff_any_measure_factorisation
      X P q a x hxa W
  rw [hLower, add_zero, hFactor] at hSplit
  exact hSplit
