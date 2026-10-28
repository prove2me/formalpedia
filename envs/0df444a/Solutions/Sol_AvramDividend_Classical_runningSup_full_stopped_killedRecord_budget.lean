-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_full_stopped_killedRecord_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:34:15.049707+00:00
-- url     : https://prove2.me/submissions/a91be093-0ca1-4123-9832-679d836b90a1

import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_full_stopped_killedRecord_budget_of_pos_ruin
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_initial_atom
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators

/-! Global pathwise killed-record budget, including instantaneous killing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q h : ℝ) (hq : 0 ≤ q) (hh : 0 < h) :
    (∫⁻ r in paymentTimes τ,
      ENNReal.ofReal (Real.exp (-(q * r)))
      ∂(dividendMeasure (runningSup X) ω)) ≤
    (∑' k : ℕ,
      if (⨅ (r : ℝ≥0) (_ : (0 : ℝ) + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) < τ then
        ENNReal.ofReal
          (h * Real.exp (-(q * ((⨅ (r : ℝ≥0) (_ : (0 : ℝ) + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞))).toReal)))
      else 0) := by
  classical
  by_cases hτ : τ = 0
  · subst τ
    have hpay : paymentTimes (0 : ℝ≥0∞) = ({0} : Set ℝ) := by
      simpa using paymentTimes_min_zero_eq_singleton_zero (0 : ℝ≥0∞)
    have hzero :
        (dividendMeasure (runningSup X) ω) ({0} : Set ℝ) = 0 :=
      runningSup_dividendMeasure_zero_initial_atom X 0 (le_refl 0) ω
    rw [hpay]
    rw [setLIntegral_measure_zero ({0} : Set ℝ)
      (fun r => ENNReal.ofReal (Real.exp (-(q * r)))) hzero]
    exact zero_le
  · have hpos : (0 : ℝ≥0∞) < τ :=
      lt_of_le_of_ne (zero_le : (0 : ℝ≥0∞) ≤ τ) (Ne.symm hτ)
    exact runningSup_full_stopped_killedRecord_budget_of_pos_ruin
      X ω τ q h hq hh hpos
