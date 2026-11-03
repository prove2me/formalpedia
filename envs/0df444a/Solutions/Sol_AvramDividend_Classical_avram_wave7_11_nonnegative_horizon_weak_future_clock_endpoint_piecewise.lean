-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_nonnegative_horizon_weak_future_clock_endpoint_piecewise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:16:14.912199+00:00
-- url     : https://prove2.me/submissions/06bd0d2c-81dc-4cae-a2e4-a9a3052e7bcf

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_weak_future_clock_exact_horizon_endpoint_correction
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Weakly future clocks retain the zero-horizon source atom,
    while positive-horizon equality clocks lose exactly the endpoint atom. -/
theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ η : ℝ≥0∞) (q T : ℝ)
    (hT : 0 ≤ T) (hFuture : ENNReal.ofReal T ≤ η) :
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    (∫⁻ t in paymentTimes (min σ η) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
    (if T = 0 then 0 else if η = ENNReal.ofReal T then
      (∫⁻ t in (paymentTimes σ ∩ Iic T) ∩ {T},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      else 0) := by
  by_cases hp : 0 < T
  · have hn : T ≠ 0 := ne_of_gt hp
    simpa only [if_neg hn] using
      (avram_wave7_11_weak_future_clock_exact_horizon_endpoint_correction
        D ω σ η q T hp hFuture)
  · have hz : T = 0 := le_antisymm (le_of_not_gt hp) hT
    subst T
    simp only [if_pos rfl, if_true, add_zero]
    calc
      (∫⁻ t in paymentTimes σ ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
        (dividendMeasure D ω) ({0} : Set ℝ) :=
          avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom D ω σ q
      _ = (∫⁻ t in paymentTimes (min σ η) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) :=
          (avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
            D ω (min σ η) q).symm
