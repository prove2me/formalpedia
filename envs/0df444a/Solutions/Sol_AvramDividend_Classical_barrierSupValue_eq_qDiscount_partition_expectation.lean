-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_eq_qDiscount_partition_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T22:41:45.590669+00:00
-- url     : https://prove2.me/submissions/02de256e-b84d-4f60-a05d-d73cbc76f4f2

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_full_partition_reward_eq_tsum

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
    (hstart : u 0 < 0) :
    barrierSupValue X a q =
      (∫⁻ ω, (∑' i : ℕ,
        ∫⁻ r in paymentTimes (barrierRuinTime X a ω),
          if r ∈ Set.Ioc (u i) (u (i + 1))
          then ENNReal.ofReal (Real.exp (-(q * r))) else 0
          ∂(dividendMeasure (runningSup X) ω)) ∂P) := by
  unfold barrierSupValue
  apply lintegral_congr
  intro ω
  have hw : Measurable (fun r : ℝ =>
      ENNReal.ofReal (Real.exp (-(q * r)))) := by
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg))
  exact runningSup_stopped_full_partition_reward_eq_tsum
    X ω (barrierRuinTime X a ω)
    (fun r => ENNReal.ofReal (Real.exp (-(q * r))))
    hw u hu hcofinal hstart
