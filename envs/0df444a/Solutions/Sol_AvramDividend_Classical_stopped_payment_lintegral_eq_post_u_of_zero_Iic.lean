-- Prove2me | solution 1 for AvramDividend.Classical.stopped_payment_lintegral_eq_post_u_of_zero_Iic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:22:22.237262+00:00
-- url     : https://prove2.me/submissions/0e9c23b7-a6e2-4e3a-81af-197c9a7967f0

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.OuterMeasure.AE
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A null pre-upcrossing interval can be deleted from a stopped dividend
integration window for arbitrary nonnegative weights. -/
theorem solution
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞) (σ : ℝ≥0∞) (u : ℝ)
    (hμzero : μ (Set.Iic u) = 0) :
    (∫⁻ t in paymentTimes σ, f t ∂μ) =
      (∫⁻ t in Set.Ioi u ∩ paymentTimes σ, f t ∂μ) := by
  have hAE : ∀ᵐ t ∂μ, t ∉ Set.Iic u := by
    apply (MeasureTheory.ae_iff).2
    simpa only [Set.Iic, Set.mem_setOf_eq, not_not] using hμzero
  apply MeasureTheory.setLIntegral_congr
  filter_upwards [hAE] with t ht
  apply propext
  constructor
  · intro h
    have hlt : u < t := lt_of_not_ge (by simpa only [Set.mem_Iic] using ht)
    exact ⟨hlt, h⟩
  · intro h
    exact h.2
