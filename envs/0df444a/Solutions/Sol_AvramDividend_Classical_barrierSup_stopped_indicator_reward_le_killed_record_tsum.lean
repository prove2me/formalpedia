-- Prove2me | solution 1 for AvramDividend.Classical.barrierSup_stopped_indicator_reward_le_killed_record_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:29:34.324982+00:00
-- url     : https://prove2.me/submissions/c328a8e6-4ec7-4c2c-b37b-5dc8a06dd690

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_full_stopped_reward_le_killed_record_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q h : ℝ)
    (hq : 0 ≤ q) (hh : 0 < h) (ω : Ω) :
    (∫⁻ t,
      if t ∈ paymentTimes (barrierRuinTime X a ω) then
        ENNReal.ofReal (Real.exp (-(q * t))) else 0
      ∂(dividendMeasure (runningSup X) ω)) ≤
    (∑' k : ℕ,
      if twoSidedExitUpTime X ((k : ℝ) * h) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (h * Real.exp (-(q *
            (twoSidedExitUpTime X ((k : ℝ) * h) ω).toReal)))
      else 0) := by
  classical
  have hr := runningSup_full_stopped_reward_le_killed_record_tsum
    X ω (barrierRuinTime X a ω) q h hq hh
  have hrewrite :
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω) then
          ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω)) =
      (∫⁻ t in paymentTimes (barrierRuinTime X a ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (runningSup X) ω)) := by
    change (∫⁻ t,
      (paymentTimes (barrierRuinTime X a ω)).indicator
        (fun r => ENNReal.ofReal (Real.exp (-(q * r)))) t
      ∂(dividendMeasure (runningSup X) ω)) = _
    exact lintegral_indicator (paymentTimes_measurable _) _
  rw [hrewrite]
  exact hr
