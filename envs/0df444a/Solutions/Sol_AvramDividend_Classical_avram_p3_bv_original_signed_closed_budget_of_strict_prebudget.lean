-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_signed_closed_budget_of_strict_prebudget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T19:10:32.495326+00:00
-- url     : https://prove2.me/submissions/a17e147c-0978-4780-b1ac-a6c614c50b5c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_canonical_signed_horizon_correction
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_strict_terminal_joint_L1_and_source_mean_le
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_full_stieltjes_reward_integrable_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- The original strict stopped W/Cash/Term inequality, once established,
implies the exact closed-horizon signed terminal budget by L1 and hjump. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0) (hS : 0 < S)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (hStrict :
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
         else 0) ∂P) ≤ w x) :
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal ∂P) +
    (∫ ω, if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * (S : ℝ))) *
        w (x + X.X S ω - rightLimit D S ω)
     else 0 ∂P) ≤ w x := by
  have hTerm := avram_p3_g2_original_BV_strict_terminal_joint_L1_and_source_mean_le
    X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad x hx hxc
    D hD q hjump S
  dsimp only at hTerm
  have hPostInt := hTerm.1
  have hPreInt := hTerm.2.1
  have hCashClosed :=
    avram_wave5_03_original_real_horizon_full_stieltjes_reward_integrable_L1
      X x C D hD (S : ℝ) S.property q
  have hCashStrict := avram_p3_bv_original_strict_cash_L1
    X x C D hD q hq (S : ℝ) S.property
  have hLe := integral_mono_ae (hCashClosed.add hPostInt)
    (hCashStrict.add hPreInt)
    (Filter.Eventually.of_forall
      (fun ω => avram_p3_c_bvchain_original_canonical_signed_horizon_correction
        X x C D hD w hjump ω S hS q hq))
  simp only [Pi.add_apply] at hLe
  rw [integral_add hCashClosed hPostInt] at hLe
  exact le_trans hLe hStrict
