-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_stopped_scale_harmonicity_general_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T17:45:16.690396+00:00
-- url     : https://prove2.me/submissions/c305e69f-1021-4b01-8fe6-3032d12e48c1

import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_stopped_scale_negative_reserve
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_stopped_scale_nonpositive_upper
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_scale_terminal_payoff_zero_of_Wzero
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_upperfirst_terminal_ofReal_lintegral_eq_scale

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Complete the original-process UBV strict two-sided stopped scale identity,
including negative reserves and both upper endpoints. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (hxa : x ≤ a) :
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
  by_cases hxNeg : x < 0
  · exact chat04_unbounded_stopped_scale_negative_reserve
      X hnbv q hq W hW a x hxa hxNeg
  · have hx0 : 0 ≤ x := le_of_not_gt hxNeg
    by_cases haNonpos : a ≤ 0
    · exact chat04_unbounded_stopped_scale_nonpositive_upper
        X hnbv q hq W hW a x hxa haNonpos
    · have ha : 0 < a := lt_of_not_ge haNonpos
      have hWzero : W 0 = 0 :=
        chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW
      calc
        _ = (∫⁻ ω, ENNReal.ofReal
            (if twoSidedExitUpTime X (a-x) ω < twoSidedExitDownTime X (-x) ω then
              Real.exp (-(q * ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
                W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω)
            else 0) ∂P) := by
              apply lintegral_congr
              intro ω
              rw [chat04_lower_exit_scale_terminal_payoff_zero_of_Wzero
                X q W hW hWzero a x ω, add_zero]
              by_cases hUp : twoSidedExitUpTime X (a-x) ω <
                  twoSidedExitDownTime X (-x) ω
              · simp only [if_pos hUp]
                exact (ENNReal.ofReal_mul (Real.exp_nonneg _)).symm
              · simp [hUp]
        _ = ENNReal.ofReal (W x) :=
          avram_root29_01_ubv_upperfirst_terminal_ofReal_lintegral_eq_scale
            X hnbv q hq W hW a x ha hx0 hxa
