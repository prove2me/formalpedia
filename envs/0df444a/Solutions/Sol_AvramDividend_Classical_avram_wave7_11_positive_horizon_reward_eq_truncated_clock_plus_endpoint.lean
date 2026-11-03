-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_positive_horizon_reward_eq_truncated_clock_plus_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:52:02.308983+00:00
-- url     : https://prove2.me/submissions/1f1caa56-42db-4ce6-8fa7-ee1b8cc23831

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_exact_horizon_endpoint_payment_set_decomposition
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_positive_horizon_endpoint_not_in_min_clock
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact strictly-positive-horizon original discounted Stieltjes decomposition:
    the strict truncated clock excludes T and the original terminal
    singleton contains precisely any dividend paid there. -/
theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℝ≥0∞) (q T : ℝ) (hT : 0 < T) :
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    (∫⁻ t in paymentTimes (min σ (ENNReal.ofReal T)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
    (∫⁻ t in (paymentTimes σ ∩ Iic T) ∩ {T},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  conv_lhs =>
    rw [avram_wave7_11_exact_horizon_endpoint_payment_set_decomposition
      σ T (le_of_lt hT)]
  have hmeas : MeasurableSet
      ((paymentTimes σ ∩ Iic T) ∩ ({T} : Set ℝ)) :=
    ((paymentTimes_measurable σ).inter measurableSet_Iic).inter
      (measurableSet_singleton T)
  have hdisj : Disjoint
      (paymentTimes (min σ (ENNReal.ofReal T)) ∩ Iic T)
      ((paymentTimes σ ∩ Iic T) ∩ ({T} : Set ℝ)) := by
    apply Set.disjoint_left.mpr
    intro t htA htB
    have hEq : t = T := htB.2
    subst t
    exact (avram_wave7_11_positive_horizon_endpoint_not_in_min_clock
      σ T hT) htA.1
  exact lintegral_union (μ := dividendMeasure D ω)
    (f := fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t)))) hmeas hdisj