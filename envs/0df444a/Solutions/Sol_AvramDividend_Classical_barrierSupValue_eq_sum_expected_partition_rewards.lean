-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_eq_sum_expected_partition_rewards
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T22:51:23.64795+00:00
-- url     : https://prove2.me/submissions/16c4aeb4-e4fe-45a1-b4e2-6735ffb1a973

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_qDiscount_partition_expectation
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ) (hu : Monotone u)
    (hcofinal : ∀ x : ℝ, ∃ n : ℕ, x ≤ u n)
    (hstart : u 0 < 0)
    (hMeas : ∀ i : ℕ, AEMeasurable
       (fun ω : Ω =>
         ∫⁻ r in paymentTimes (barrierRuinTime X a ω),
           if r ∈ Set.Ioc (u i) (u (i + 1))
           then ENNReal.ofReal (Real.exp (-(q * r))) else 0
           ∂(dividendMeasure (runningSup X) ω)) P) :
    barrierSupValue X a q =
    (∑' i : ℕ,
      ∫⁻ ω, (
        ∫⁻ r in paymentTimes (barrierRuinTime X a ω),
          if r ∈ Set.Ioc (u i) (u (i + 1))
          then ENNReal.ofReal (Real.exp (-(q * r))) else 0
          ∂(dividendMeasure (runningSup X) ω)) ∂P) := by
  calc
    barrierSupValue X a q =
      (∫⁻ ω, (∑' i : ℕ,
        ∫⁻ r in paymentTimes (barrierRuinTime X a ω),
          if r ∈ Set.Ioc (u i) (u (i + 1))
          then ENNReal.ofReal (Real.exp (-(q * r))) else 0
          ∂(dividendMeasure (runningSup X) ω)) ∂P) :=
       barrierSupValue_eq_qDiscount_partition_expectation
         X a q hq u hu hcofinal hstart
    _ = (∑' i : ℕ,
      ∫⁻ ω, (
        ∫⁻ r in paymentTimes (barrierRuinTime X a ω),
          if r ∈ Set.Ioc (u i) (u (i + 1))
          then ENNReal.ofReal (Real.exp (-(q * r))) else 0
          ∂(dividendMeasure (runningSup X) ω)) ∂P) := by
      exact MeasureTheory.lintegral_tsum hMeas
