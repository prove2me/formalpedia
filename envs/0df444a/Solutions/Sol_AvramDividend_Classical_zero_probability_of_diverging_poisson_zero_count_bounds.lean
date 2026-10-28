-- Prove2me | solution 1 for AvramDividend.Classical.zero_probability_of_diverging_poisson_zero_count_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:55:08.290004+00:00
-- url     : https://prove2.me/submissions/a31bcd5c-6baf-438e-b44a-4235d2bd74e6

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Basic

open MeasureTheory Set Filter
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (rates : ℕ → ℝ)
    (hrates : Tendsto rates atTop atTop)
    (hbound : ∀ n : ℕ, (P A).toReal ≤ Real.exp (-(rates n))) :
    P A = 0 := by
  have hlim : Tendsto (fun n => Real.exp (-(rates n))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hrates
  have h0 : (P A).toReal ≤ 0 := ge_of_tendsto' hlim hbound
  have h1 : (P A).toReal = 0 := le_antisymm h0 ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_eq_zero_iff _).1 h1 with h | h
  · exact h
  · exact absurd h (measure_ne_top P A)
