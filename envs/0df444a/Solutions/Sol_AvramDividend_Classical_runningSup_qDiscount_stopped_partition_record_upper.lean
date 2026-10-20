-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_qDiscount_stopped_partition_record_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T22:41:48.874894+00:00
-- url     : https://prove2.me/submissions/2efb9724-994e-488d-95b4-667660e79ffb

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_full_partition_reward_eq_tsum
import Theorems.Thm_AvramDividend_Classical_runningSup_qDiscount_countable_partition_sum_bounds

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
      ∂(dividendMeasure (runningSup X) ω)) ≤
    (∑' i : ℕ,
      ENNReal.ofReal (Real.exp (-(q * u i))) *
      ENNReal.ofReal
        (runningSup X (u (i + 1)).toNNReal ω -
         runningSup X (u i).toNNReal ω)) := by
  have hw : Measurable (fun r : ℝ =>
      ENNReal.ofReal (Real.exp (-(q * r)))) := by
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg))
  rw [runningSup_stopped_full_partition_reward_eq_tsum
    X ω τ (fun r => ENNReal.ofReal (Real.exp (-(q * r))))
    hw u hu hcofinal hstart]
  calc
    (∑' i : ℕ,
      ∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc (u i) (u (i + 1))
          then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤
    (∑' i : ℕ,
      ∫⁻ r,
        if r ∈ Set.Ioc (u i) (u (i + 1))
          then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) := by
      apply ENNReal.tsum_le_tsum
      intro i
      have hi :
        (∫⁻ r in paymentTimes τ,
          if r ∈ Set.Ioc (u i) (u (i + 1))
            then ENNReal.ofReal (Real.exp (-(q * r))) else 0
          ∂(dividendMeasure (runningSup X) ω)) ≤
        (∫⁻ r in (Set.univ : Set ℝ),
          if r ∈ Set.Ioc (u i) (u (i + 1))
            then ENNReal.ofReal (Real.exp (-(q * r))) else 0
          ∂(dividendMeasure (runningSup X) ω)) := by
          apply lintegral_mono_set
          exact Set.subset_univ _
      simpa only [setLIntegral_univ] using hi
    _ ≤ (∑' i : ℕ,
      ENNReal.ofReal (Real.exp (-(q * u i))) *
      ENNReal.ofReal
        (runningSup X (u (i + 1)).toNNReal ω -
         runningSup X (u i).toNNReal ω)) :=
       (runningSup_qDiscount_countable_partition_sum_bounds
         X ω q hq u).2
