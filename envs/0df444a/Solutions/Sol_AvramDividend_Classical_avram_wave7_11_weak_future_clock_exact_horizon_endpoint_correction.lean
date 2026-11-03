-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_weak_future_clock_exact_horizon_endpoint_correction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:12:18.776921+00:00
-- url     : https://prove2.me/submissions/e3cd1d9a-1400-4234-825f-dbd697b2fb9e

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_positive_horizon_reward_eq_truncated_clock_plus_endpoint
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_strict_future_clock_preserves_finite_payment_set
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A weakly future auxiliary clock preserves the exact source
    Stieltjes cash up to the sole explicit missing terminal singleton. -/
theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ η : ℝ≥0∞) (q T : ℝ)
    (hT : 0 < T) (hFuture : ENNReal.ofReal T ≤ η) :
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    (∫⁻ t in paymentTimes (min σ η) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
    (if η = ENNReal.ofReal T then
      (∫⁻ t in (paymentTimes σ ∩ Iic T) ∩ {T},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      else 0) := by
  rcases eq_or_lt_of_le hFuture with heq | hgt
  · subst η
    simpa only [if_pos rfl, if_true] using
      (avram_wave7_11_positive_horizon_reward_eq_truncated_clock_plus_endpoint
        D ω σ q T hT)
  · have hne : η ≠ ENNReal.ofReal T := ne_of_gt hgt
    simp only [if_neg hne, add_zero]
    rw [avram_wave7_11_strict_future_clock_preserves_finite_payment_set
      σ η T hgt]
