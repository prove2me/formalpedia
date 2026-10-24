-- Prove2me | solution 1 for AvramDividend.Classical.discounted_dividend_window_real_lintegral_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:09:17.81441+00:00
-- url     : https://prove2.me/submissions/3a318057-4c68-47f1-846a-3094815c79b8

import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_finite_measure_payout_bridge
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_zero_eq_dividendValue
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- On genuine finite-horizon dividend windows, the real Stieltjes discount
    integral is integrable and agrees with the extended-real payoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞) (T : ℝ≥0) (ω : Ω) :
    (∫⁻ t in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      ENNReal.ofReal
        (∫ t in paymentTimes σ ∩ Iic (T : ℝ),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by
  have hTsucc : (T : ℝ) < ((T + 1 : ℝ≥0) : ℝ) := by
    exact_mod_cast
      (lt_add_of_pos_right T (by norm_num : (0 : ℝ≥0) < 1))
  have hsubset :
      paymentTimes σ ∩ Iic (T : ℝ) ⊆
        Ico (0 : ℝ) ((T + 1 : ℝ≥0) : ℝ) := by
    intro t ht
    exact ⟨ht.1.1, lt_of_le_of_lt ht.2 hTsucc⟩
  have hmass := measure_mono (μ := dividendMeasure D ω) hsubset
  rw [dividendMeasure_Ico_zero_eq_dividendValue D hD ω (T + 1)] at hmass
  have hfin : ENNReal.ofReal (D (T + 1) ω) < ⊤ := by simp
  have hwindow : dividendMeasure D ω
      (paymentTimes σ ∩ Iic (T : ℝ)) ≠ ⊤ :=
    (lt_of_le_of_lt hmass hfin).ne
  apply discounted_stieltjes_finite_measure_payout_bridge q hq
    (dividendMeasure D ω) (paymentTimes σ ∩ Iic (T : ℝ))
  · exact (paymentTimes_measurable σ).inter measurableSet_Iic
  · intro t ht
    exact ht.1.1
  · exact hwindow
