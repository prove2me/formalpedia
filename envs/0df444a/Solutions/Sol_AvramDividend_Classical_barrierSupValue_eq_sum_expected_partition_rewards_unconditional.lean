-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_eq_sum_expected_partition_rewards_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T15:34:58.801805+00:00
-- url     : https://prove2.me/submissions/490b68f9-930b-437e-a3f8-6128645c104c

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Theorems.Thm_AvramDividend_Classical_lintegral_two_restrictions_commute
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_Ioc_reward_measurable
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_sum_expected_partition_rewards

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ) (hu : Monotone u)
    (hcofinal : ∀ x : ℝ, ∃ n : ℕ, x ≤ u n)
    (hstart : u 0 < 0) :
    barrierSupValue X a q =
    (∑' i : ℕ,
      ∫⁻ ω, (
        ∫⁻ r in paymentTimes (barrierRuinTime X a ω),
          if r ∈ Set.Ioc (u i) (u (i + 1))
          then ENNReal.ofReal (Real.exp (-(q * r))) else 0
          ∂(dividendMeasure (runningSup X) ω)) ∂P) := by
  have hEq (i : ℕ) (ω : Ω) :
      (∫⁻ r in paymentTimes (barrierRuinTime X a ω),
        if r ∈ Set.Ioc (u i) (u (i + 1))
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) =
      (∫⁻ r,
        if r ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω).restrict
          (Set.Ioc (u i) (u (i + 1)))) := by
    have hraw := lintegral_two_restrictions_commute
      (dividendMeasure (runningSup X) ω)
      (paymentTimes (barrierRuinTime X a ω))
      (Set.Ioc (u i) (u (i + 1)))
      (paymentTimes_measurable _)
      measurableSet_Ioc
      (fun r : ℝ => ENNReal.ofReal (Real.exp (-(q * r))))
    refine Eq.trans ?_ hraw
    apply lintegral_congr
    intro r
    by_cases hr : r ∈ Set.Ioc (u i) (u (i + 1))
    · simp [hr]
    · simp [hr]
  have hMeas (i : ℕ) :
      AEMeasurable (fun ω : Ω =>
        ∫⁻ r in paymentTimes (barrierRuinTime X a ω),
          if r ∈ Set.Ioc (u i) (u (i + 1))
          then ENNReal.ofReal (Real.exp (-(q * r))) else 0
          ∂(dividendMeasure (runningSup X) ω)) P := by
    have hFun :
        (fun ω : Ω =>
          ∫⁻ r in paymentTimes (barrierRuinTime X a ω),
            if r ∈ Set.Ioc (u i) (u (i + 1))
            then ENNReal.ofReal (Real.exp (-(q * r))) else 0
            ∂(dividendMeasure (runningSup X) ω)) =
        (fun ω : Ω =>
          ∫⁻ r,
            if r ∈ paymentTimes (barrierRuinTime X a ω)
            then ENNReal.ofReal (Real.exp (-(q * r))) else 0
            ∂(dividendMeasure (runningSup X) ω).restrict
              (Set.Ioc (u i) (u (i + 1)))) := by
      funext ω
      exact hEq i ω
    rw [hFun]
    exact (runningSup_stopped_Ioc_reward_measurable
      X a q (u i) (u (i + 1))).aemeasurable
  exact barrierSupValue_eq_sum_expected_partition_rewards
    X a q hq u hu hcofinal hstart hMeas
