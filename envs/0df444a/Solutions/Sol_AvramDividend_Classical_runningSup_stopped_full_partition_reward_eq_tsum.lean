-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_stopped_full_partition_reward_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T22:26:57.772673+00:00
-- url     : https://prove2.me/submissions/dec604cc-2e4f-4c2b-b03c-fdc900ddaf21

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Data.Set.Insert
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_partition_reward_eq_tsum

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
    (τ : ℝ≥0∞) (w : ℝ → ℝ≥0∞) (hw : Measurable w)
    (u : ℕ → ℝ) (hu : Monotone u)
    (hcofinal : ∀ x : ℝ, ∃ n : ℕ, x ≤ u n)
    (hstart : u 0 < 0) :
    (∫⁻ r in paymentTimes τ, w r
      ∂(dividendMeasure (runningSup X) ω)) =
    (∑' i : ℕ,
       ∫⁻ r in paymentTimes τ,
         if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0
         ∂(dividendMeasure (runningSup X) ω)) := by
  have hset : MeasurableSet (paymentTimes τ) := by
    change MeasurableSet
      {r : ℝ | 0 ≤ r ∧ (r = 0 ∨ ENNReal.ofReal r < τ)}
    have hz : MeasurableSet {r : ℝ | r = 0} := by
      simpa only [Set.setOf_eq_eq_singleton] using
        (MeasurableSet.singleton (0 : ℝ))
    have hlt : MeasurableSet {r : ℝ | ENNReal.ofReal r < τ} :=
      ENNReal.measurable_ofReal measurableSet_Iio
    exact measurableSet_Ici.inter (hz.union hlt)
  have hbefore :
      ∀ᵐ r ∂ (dividendMeasure (runningSup X) ω).restrict (paymentTimes τ),
        u 0 < r := by
    filter_upwards [ae_restrict_mem hset] with r hr
    have h0 : (0 : ℝ) ≤ r := by
      change 0 ≤ r ∧ (r = 0 ∨ ENNReal.ofReal r < τ) at hr
      exact hr.1
    exact lt_of_lt_of_le hstart h0
  calc
    (∫⁻ r in paymentTimes τ, w r
      ∂(dividendMeasure (runningSup X) ω)) =
      (∫⁻ r in paymentTimes τ, if u 0 < r then w r else 0
        ∂(dividendMeasure (runningSup X) ω)) := by
          apply lintegral_congr_ae
          filter_upwards [hbefore] with r hr
          simp only [if_pos hr]
    _ = (∑' i : ℕ,
        ∫⁻ r in paymentTimes τ,
          if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0
          ∂(dividendMeasure (runningSup X) ω)) :=
      runningSup_stopped_partition_reward_eq_tsum X ω τ w hw u hu hcofinal
