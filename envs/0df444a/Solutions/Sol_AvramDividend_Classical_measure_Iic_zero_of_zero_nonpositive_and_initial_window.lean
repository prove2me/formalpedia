-- Prove2me | solution 1 for AvramDividend.Classical.measure_Iic_zero_of_zero_nonpositive_and_initial_window
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:50:01.434111+00:00
-- url     : https://prove2.me/submissions/c187cfa3-5813-4bcc-8272-fc888880f262

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.MeasureSpace

open MeasureTheory Set
open scoped ENNReal
theorem solution
    (μ : Measure ℝ) (u : ℝ)
    (hnegative : μ (Set.Iic (0 : ℝ)) = 0)
    (hthrough : μ (Set.Icc (0 : ℝ) u) = 0) :
    μ (Set.Iic u) = 0 := by
  refine measure_mono_null (fun x (hx : x ≤ u) => ?_) (measure_union_null hnegative hthrough)
  rcases le_total x 0 with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, hx⟩
