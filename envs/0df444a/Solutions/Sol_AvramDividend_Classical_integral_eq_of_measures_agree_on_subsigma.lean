-- Prove2me | solution 1 for AvramDividend.Classical.integral_eq_of_measures_agree_on_subsigma
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:59:52.256786+00:00
-- url     : https://prove2.me/submissions/7358c302-19fe-4624-9251-331d99648db0

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Trim
open MeasureTheory
theorem solution
    {Ω : Type*} [m0 : MeasurableSpace Ω]
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    (μ ν : Measure Ω)
    (hset : ∀ A : Set Ω, @MeasurableSet Ω m A → μ A = ν A)
    (f : Ω → ℝ) (hf : StronglyMeasurable[m] f) :
    (∫ ω, f ω ∂μ) = (∫ ω, f ω ∂ν) := by
  have h : μ = ν := Measure.ext fun A hA => hset A hA
  rw [h]
