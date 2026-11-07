-- Prove2me | solution 8 for AvramDividend.Classical.admissible_cap_truncated_ubv_stochastic_core_corrected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:44:43.389231+00:00
-- url     : https://prove2.me/submissions/19b15af2-8bd0-4e1f-97e2-10df3720acdc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_corrected_ubv_zeroCap_or_zeroHorizon
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_ito_residual_given_real_stopped_clock
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_original_raw_signed_residual_to_full_cash
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_natural_ruin_clock_full_stopping_package
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_actual_truncated_clock_real_measurable_of_source
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_admissible_initial_reserve_nonnegative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
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
  by_cases hC0 : C = 0
  · exact avram_wave5_05_corrected_ubv_zeroCap_or_zeroHorizon
      X hX hBV q hq w C hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x hxc D hD hw_nonneg hjump T hT (Or.inl hC0)
  have hCpos : (0 : ℝ≥0∞) < C := lt_of_le_of_ne bot_le (Ne.symm hC0)
  have hx : 0 ≤ x :=
    avram_sweep16_20261106_admissible_initial_reserve_nonnegative X x C D hD
  by_cases hx0 : x = 0
  · subst x
    exact avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
      X hBV q w C hw0 hw_cont hw_smooth hw_grad D hD hjump T hT
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hClock :=
    avram_sweep16_20261106_natural_ruin_clock_full_stopping_package X x C D hD
  have hRuinMeas : Measurable (ruinTime X x D) :=
    ruinTime_measurable X x D hD.1.1
  have hRaw := fun (n : ℕ) (hn : 0 < n) =>
    avram_wave7_08_source_ito_residual_given_real_stopped_clock
      X hX hBV q hq w C hCpos hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hxpos hxc D hD hw_nonneg hjump n hn
      (fun ω => (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
      (by intro ω; rfl)
      (avram_wave7_08_actual_truncated_clock_real_measurable_of_source
        X x D n hRuinMeas)
      (hClock n hn).2.1
  exact avram_sweep16_20261106_original_raw_signed_residual_to_full_cash
    X hBV q hq w C hCpos hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
    x hx hxc D hD T hRaw
