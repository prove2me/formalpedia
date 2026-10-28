-- Prove2me | solution 1 for AvramDividend.Classical.drained_zero_barrier_no_nonpositive_expected_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:56:33.694828+00:00
-- url     : https://prove2.me/submissions/afc42dd4-acb8-41e0-8558-2ce858f3c27c

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_drained_zero_barrier_expected_reward_lower_bound
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A strictly positive initial lump sum rules out any nonpositive
    proposed expectation upper bound, even when ruin is immediate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 < x)
    (w : ℝ → ℝ) (hwx : w x ≤ 0)
    (q T : ℝ) (hT : 0 ≤ T) :
    ¬ ((∫⁻ ω, ∫⁻ t in paymentTimes
        (ruinTime X x
          (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure
          (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) ω) ∂P) ≤
      ENNReal.ofReal (w x)) := by
  intro hbound
  have hge : ENNReal.ofReal x ≤
      (∫⁻ ω, ∫⁻ t in paymentTimes
        (ruinTime X x
          (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure
            (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) ω) ∂P) :=
    drained_zero_barrier_expected_reward_lower_bound X x (le_of_lt hx) q T hT
  have hwzero : ENNReal.ofReal (w x) = 0 :=
    ENNReal.ofReal_eq_zero.mpr hwx
  have hxzero : ENNReal.ofReal x ≤ 0 := by
    exact le_trans hge (by simpa only [hwzero] using hbound)
  exact (not_le_of_gt (ENNReal.ofReal_pos.mpr hx)) hxzero
