-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_minimal_original_ubv_one_clock_value_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:07:58.502286+00:00
-- url     : https://prove2.me/submissions/5ea72211-0109-4487-9ff2-5337a17339c7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_ubv_zero_start_original_full_discounted_stieltjes_reward_eq_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_one_future_natural_ruin_clock_budget_controls_full_finite_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hw0 : 0 ≤ w 0)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (hOneClock : 0 < x →
      ∃ n : ℕ, T < (n : ℝ) ∧
        (∫⁻ ω, ∫⁻ t in paymentTimes
          (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  by_cases hxzero : x = 0
  · subst x
    have hzero :
        (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) = 0 :=
      avram_wave6_08_ubv_zero_start_original_full_discounted_stieltjes_reward_eq_zero
        X hBV q C D hD ⟨T, hT⟩
    rw [hzero]
    exact bot_le
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
    obtain ⟨n, hFuture, hBound⟩ := hOneClock hxpos
    exact avram_wave7_11_one_future_natural_ruin_clock_budget_controls_full_finite_horizon
      X x D q T n hT hFuture (ENNReal.ofReal (w x)) hBound
