-- Prove2me | solution 6 for AvramDividend.Classical.admissible_cap_truncated_ubv_stochastic_core_corrected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T08:08:25.524139+00:00
-- url     : https://prove2.me/submissions/a626d8fb-9e59-4647-bbf7-2c01a4562122
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_corrected_ubv_zeroCap_fullHorizon_allInitialCapital
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_allCap_admissible_initial_capital_nonneg
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_zero_bounded_clock_exact_stieltjes_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_ubv_positive_n_bounded_ruin_clock_ito_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_corrected_ubv_from_actual_bounded_ruin_budgets

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

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
  have hx : 0 ≤ x :=
    avram_wave3_04_allCap_admissible_initial_capital_nonneg X x C hxc D hD
  by_cases hCzero : C = 0
  · subst C
    exact avram_wave3_04_corrected_ubv_zeroCap_fullHorizon_allInitialCapital
      X hBV w hw0 x hxc D hD q T hT
  by_cases hxzero : x = 0
  · subst x
    exact avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
      X hBV q w C hw0 hw_cont hw_smooth hw_grad D hD hjump T hT
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
  have hCpos : (0 : ℝ≥0∞) < C :=
    lt_of_le_of_ne bot_le (Ne.symm hCzero)
  apply avram_wave5_05_corrected_ubv_from_actual_bounded_ruin_budgets
    X hX hBV q hq w C hw0 hw_cont hw_neg hw_smooth
    hw_gen hw_grad x hxc D hD hw_nonneg hjump T hT
  intro n
  cases n with
  | zero =>
      simpa only [Nat.cast_zero] using
        avram_wave7_08_zero_bounded_clock_exact_stieltjes_budget
          X q x w C hw0 hw_cont hw_smooth hw_grad D hD hxc hjump T hT
  | succ k =>
      exact avram_wave7_08_ubv_positive_n_bounded_ruin_clock_ito_budget
        X hX hBV q hq w C hCpos hw0 hw_cont hw_neg hw_smooth
        hw_gen hw_grad x hxpos hxc D hD hw_nonneg hjump
        T hT (Nat.succ k) (Nat.zero_lt_succ k)
