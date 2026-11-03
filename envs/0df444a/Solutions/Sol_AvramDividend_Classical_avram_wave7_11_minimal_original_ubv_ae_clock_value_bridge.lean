-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_minimal_original_ubv_ae_clock_value_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:57:47.730103+00:00
-- url     : https://prove2.me/submissions/14c3645b-f49d-46c6-9559-76140b4f860a

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_ubv_zero_start_original_full_discounted_stieltjes_reward_eq_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_ae_future_ruin_clock_budget_controls_original_horizon
import Mathlib.Data.Real.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact original-process expectation transfer from a single almost
    surely late random clock, requiring no standing, HJB or C2 hypotheses
    beyond a source stopped-cash budget at positive reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hw0 : 0 ≤ w 0)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (hAeClock : 0 < x →
      ∃ η : Ω → ℝ≥0∞,
        (∀ᵐ ω ∂P, ENNReal.ofReal T < η ω) ∧
        (∫⁻ ω, ∫⁻ t in paymentTimes
          (min (ruinTime X x D ω) (η ω)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  rcases eq_or_lt_of_le hx with hzero | hpos
  · subst x
    have hZero :
        (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) = 0 := by
      exact avram_wave6_08_ubv_zero_start_original_full_discounted_stieltjes_reward_eq_zero
        X hBV q C D hD (⟨T, hT⟩ : ℝ≥0)
    rw [hZero]
    exact bot_le
  · obtain ⟨η, hFuture, hBudget⟩ := hAeClock hpos
    exact avram_wave7_11_ae_future_ruin_clock_budget_controls_original_horizon
      X x D q T η hFuture (ENNReal.ofReal (w x)) hBudget
