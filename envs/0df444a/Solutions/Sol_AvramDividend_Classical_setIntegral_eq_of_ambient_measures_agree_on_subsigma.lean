-- Prove2me | solution 1 for AvramDividend.Classical.setIntegral_eq_of_ambient_measures_agree_on_subsigma
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:12:18.582916+00:00
-- url     : https://prove2.me/submissions/8dfc3e21-73af-4a02-a8e1-c4c214a3de2b

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
theorem solution
    {Ω : Type*} [m0 : MeasurableSpace Ω]
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    (μ ν : @Measure Ω m0)
    (hset : ∀ B : Set Ω, @MeasurableSet Ω m B → μ B = ν B)
    (A : Set Ω) (hA : @MeasurableSet Ω m A)
    (f : Ω → ℝ) (hf : StronglyMeasurable[m] f) :
    (∫ ω in A, f ω ∂μ) = (∫ ω in A, f ω ∂ν) := by
  have ht : μ.trim hm = ν.trim hm := by
    refine @Measure.ext _ m _ _ (fun t htm => ?_)
    rw [trim_measurableSet_eq hm htm, trim_measurableSet_eq hm htm, hset t htm]
  rw [integral_trim hm hf, integral_trim hm hf, ← restrict_trim hm μ hA,
    ← restrict_trim hm ν hA, ht]
