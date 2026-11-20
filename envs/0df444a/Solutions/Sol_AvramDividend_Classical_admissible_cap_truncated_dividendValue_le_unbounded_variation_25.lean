-- Prove2me | solution 25 for AvramDividend.Classical.admissible_cap_truncated_dividendValue_le_unbounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:39:39.176179+00:00
-- url     : https://prove2.me/submissions/b225d4e7-479e-4f05-b6dd-a0619568bd67
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_original_right_payment_secant_from_gradient
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_corrected_boundary_hjb_pre_ruin_terminal_nonneg
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_diagonal_nat_clock_cash_budget_implies_full_closed_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_ubv_positive_n_positive_horizon_source_ito_budget
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  classical
  have hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0 := by
    intro y hy hyC
    constructor
    · exact (hw_hjb y hy hyC).1
    · calc
        X.generator w y - q * w y ≤
            max (X.generator w y - q * w y) (1 - deriv w y) :=
          le_max_left _ _
        _ = 0 := (hw_hjb y hy hyC).2
  have hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y := by
    intro y hy hyC
    have hle : 1 - deriv w y ≤ 0 := by
      calc
        1 - deriv w y ≤
            max (X.generator w y - q * w y) (1 - deriv w y) :=
          le_max_right _ _
        _ = 0 := (hw_hjb y hy hyC).2
    linarith
  have hjump :=
    AvramDividend.Classical.avram_sweep16_20261106_original_right_payment_secant_from_gradient
      X x C hC hxc D hD w hw_cont hw_smooth hw_grad
  have hSmooth1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hw_smooth.of_le (by norm_num)
  have hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω) := by
    intro ω t ht hruin
    exact
      AvramDividend.Classical.avram_wave6_08_original_corrected_boundary_hjb_pre_ruin_terminal_nonneg
        X x C hC hxc D hD w hw0 hw_cont hSmooth1 hw_grad ω t hruin
  by_cases hx0 : x = 0
  · subst x
    exact
      AvramDividend.Classical.avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
        X hBV q w C hw0 hw_cont hw_smooth hw_grad
        D hD hjump T hT
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    apply AvramDividend.Classical.avram_ubv_hor3_original_diagonal_nat_clock_cash_budget_implies_full_closed_horizon
      X x q T D (ENNReal.ofReal (w x))
    intro n hn
    have hTpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact
      AvramDividend.Classical.avram_wave7_08_ubv_positive_n_positive_horizon_source_ito_budget
        X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
        x hxpos hxc D hD hw_nonneg hjump
        (n : ℝ) hTpos n hn
