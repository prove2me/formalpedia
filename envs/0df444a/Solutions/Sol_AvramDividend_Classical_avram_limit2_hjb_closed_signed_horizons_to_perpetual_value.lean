-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_hjb_closed_signed_horizons_to_perpetual_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:06:11.749989+00:00
-- url     : https://prove2.me/submissions/ab3d5b82-d000-47eb-8bd4-eb40a9457376

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit1_bv_original_signed_horizons_and_terminal_to_dividendValue
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Uniform original closed-cash signed stopped budgets imply an integrable
    postpayment terminal at every positive horizon and bound perpetual value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hBudget : ∀ (T : ℝ) (hT : 0 ≤ T), 0 < T →
      let S : ℝ≥0 := ⟨T, hT⟩
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0) ∂P) ≤ w x) :
    (∀ (T : ℝ) (hT : 0 ≤ T), 0 < T →
      let S : ℝ≥0 := ⟨T, hT⟩
      Integrable (fun ω => (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0)) P) ∧
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
  have hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y := by
    intro y hy hyc
    obtain ⟨_, hmax⟩ := hw_hjb y hy hyc
    have hBound := le_max_right (X.generator w y - q * w y) (1 - deriv w y)
    rw [hmax] at hBound
    linarith
  have hjump :=
    avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
      X C hC w hw_cont hw_smooth hwGrad x hxc D hD
  exact avram_limit1_bv_original_signed_horizons_and_terminal_to_dividendValue
    X hBV q (le_of_lt hq) w C hC hw_cont hw0 hw_neg hw_smooth
    hwGrad x hx hxc D hD hjump (w x) hBudget
