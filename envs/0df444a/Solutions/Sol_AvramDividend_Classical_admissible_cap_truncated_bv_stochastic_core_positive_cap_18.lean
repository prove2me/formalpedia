-- Prove2me | solution 18 for AvramDividend.Classical.admissible_cap_truncated_bv_stochastic_core_positive_cap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:09:22.464048+00:00
-- url     : https://prove2.me/submissions/875b48a8-590e-4303-876b-e7fea88a6261
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_stopped_HJB_budget
import Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_signed_horizon_real_perpetual_bridge
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_finite_ruin_cash_le_perpetual_value
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Derive finite original stopped cash from signed horizons and perpetual value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hwLower := avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
    C hC w hw_cont hw_smooth hw_grad x hx hxc x ⟨hx, le_refl x⟩
  have hwx : 0 ≤ w x := by linarith
  have hBudget (s : ℝ) (hs : 0 ≤ s) (hspos : 0 < s) :
      let S : ℝ≥0 := ⟨s, hs⟩
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic s,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * s)) * w (x + X.X S ω - rightLimit D S ω)
       else 0) ∂P) ≤ w x := by
    exact avram_wave8_04_original_BV_positive_horizon_signed_stopped_HJB_budget
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump s hs hspos
  have hBridge := avram_limit2_bv_signed_horizon_real_perpetual_bridge
    X hBV q (le_of_lt hq) w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
    x hx hxc D hD hjump (w x) hwx hBudget
  exact (avram_sweep16_original_finite_ruin_cash_le_perpetual_value
    X q x D hD.1 T).trans hBridge.2.1
