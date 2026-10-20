-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_qDiscount_stopped_full_partition_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T22:36:22.036149+00:00
-- url     : https://prove2.me/submissions/a4934a1e-6bce-4eb8-9797-317a89f5aa9c

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
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ) (hu : Monotone u)
    (hcofinal : ∀ x : ℝ, ∃ n : ℕ, x ≤ u n)
    (hstart : u 0 < 0) :
    (∫⁻ r in paymentTimes τ,
       ENNReal.ofReal (Real.exp (-(q * r)))
       ∂(dividendMeasure (runningSup X) ω)) =
    (∑' i : ℕ,
       ∫⁻ r in paymentTimes τ,
         if r ∈ Set.Ioc (u i) (u (i + 1))
         then ENNReal.ofReal (Real.exp (-(q * r))) else 0
         ∂(dividendMeasure (runningSup X) ω)) := by
  have hw : Measurable (fun r : ℝ =>
      ENNReal.ofReal (Real.exp (-(q * r)))) := by
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg))
  exact runningSup_stopped_full_partition_reward_eq_tsum
    X ω τ (fun r => ENNReal.ofReal (Real.exp (-(q * r))))
    hw u hu hcofinal hstart
