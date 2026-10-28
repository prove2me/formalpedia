-- Prove2me | solution 1 for AvramDividend.Classical.integrable_iff_of_ambient_measures_agree_on_subsigma
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:14:52.729459+00:00
-- url     : https://prove2.me/submissions/8145fb40-1634-48dc-b1a2-2dfda9c525ba

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Trim
open MeasureTheory

theorem solution
    {Ω : Type*} [m0 : MeasurableSpace Ω]
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    (μ ν : @Measure Ω m0)
    (hset : ∀ B : Set Ω, @MeasurableSet Ω m B → μ B = ν B)
    (f : Ω → ℝ) (hf : StronglyMeasurable[m] f) :
    Integrable f μ ↔ Integrable f ν := by
  have ht : μ.trim hm = ν.trim hm := by
    refine @Measure.ext _ m _ _ (fun t htm => ?_)
    rw [trim_measurableSet_eq hm htm, trim_measurableSet_eq hm htm, hset t htm]
  constructor
  · intro h
    have := h.trim hm hf
    rw [ht] at this
    exact integrable_of_integrable_trim hm this
  · intro h
    have := h.trim hm hf
    rw [← ht] at this
    exact integrable_of_integrable_trim hm this
