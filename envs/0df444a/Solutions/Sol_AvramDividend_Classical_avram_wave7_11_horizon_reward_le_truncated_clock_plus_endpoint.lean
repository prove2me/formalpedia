-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_horizon_reward_le_truncated_clock_plus_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:18:01.71414+00:00
-- url     : https://prove2.me/submissions/621f172a-7b42-48ea-95d9-171dfc29ef85

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_exact_horizon_endpoint_payment_set_decomposition
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact terminal-atom remainder bound, preserving the original measure. -/
theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℝ≥0∞) (q T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    (∫⁻ t in paymentTimes (min σ (ENNReal.ofReal T)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
    (∫⁻ t in (paymentTimes σ ∩ Iic T) ∩ {T},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  conv_lhs =>
    rw [avram_wave7_11_exact_horizon_endpoint_payment_set_decomposition
      σ T hT]
  exact lintegral_union_le
    (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t))))
    (paymentTimes (min σ (ENNReal.ofReal T)) ∩ Iic T)
    ((paymentTimes σ ∩ Iic T) ∩ {T})
