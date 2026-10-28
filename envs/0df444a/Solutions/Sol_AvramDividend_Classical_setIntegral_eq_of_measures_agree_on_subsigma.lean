-- Prove2me | solution 1 for AvramDividend.Classical.setIntegral_eq_of_measures_agree_on_subsigma
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T22:56:29.02522+00:00
-- url     : https://prove2.me/submissions/2a26884c-4cc1-4e66-9b42-c3f374ca1972

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Theorems.Thm_AvramDividend_Classical_integral_eq_of_measures_agree_on_subsigma
open MeasureTheory Set
theorem solution
    {Ω : Type*} [m0 : MeasurableSpace Ω]
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    (μ ν : Measure Ω)
    (hset : ∀ B : Set Ω, @MeasurableSet Ω m B → μ B = ν B)
    (A : Set Ω) (hA : @MeasurableSet Ω m A)
    (f : Ω → ℝ) (hf : StronglyMeasurable[m] f) :
    (∫ ω in A, f ω ∂μ) = (∫ ω in A, f ω ∂ν) := by
  rw [← integral_indicator hA, ← integral_indicator hA]
  exact AvramDividend.Classical.integral_eq_of_measures_agree_on_subsigma le_rfl μ ν hset _
    (hf.indicator hA)
