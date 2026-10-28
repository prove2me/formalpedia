-- Prove2me | solution 1 for AvramDividend.Classical.lintegral_killed_window_translation_of_measure_map
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:32:19.372882+00:00
-- url     : https://prove2.me/submissions/bb670611-6611-4b16-b353-26cc8a278183

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict

open MeasureTheory Set
open scoped ENNReal
theorem solution
    (μ ν : Measure ℝ) (u : ℝ) (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμ : μ = Measure.map (fun t : ℝ => u + t) ν)
    (hwindow : ∀ t : ℝ, u + t ∈ A ↔ t ∈ B)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ t in A, f t ∂μ) =
      ∫⁻ t in B, f (u + t) ∂ν := by
  have e : (fun t : ℝ => u + t) ⁻¹' A = B := by
    ext t; exact hwindow t
  rw [hμ, setLIntegral_map hA hf (measurable_const_add u), e]
