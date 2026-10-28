-- Prove2me | solution 1 for AvramDividend.Classical.probability_uniform_mesh_bound_to_real
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:42:49.764656+00:00
-- url     : https://prove2.me/submissions/c1bb2cb6-75e1-4045-9ec1-ab387c19e12d

import Mathlib
open MeasureTheory
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Set Ω) (N : ℕ)
    (hBound : P A ≤ (N : ℝ≥0∞) * P B) :
    P.real A ≤ (N : ℝ) * P.real B := by
  have hfin : (N : ℝ≥0∞) * P B ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) (measure_ne_top P B)
  have := ENNReal.toReal_mono hfin hBound
  simpa [Measure.real, ENNReal.toReal_mul] using this
