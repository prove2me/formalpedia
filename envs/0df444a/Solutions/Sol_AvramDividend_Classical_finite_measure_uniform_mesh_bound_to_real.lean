-- Prove2me | solution 1 for AvramDividend.Classical.finite_measure_uniform_mesh_bound_to_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T15:18:14.3303+00:00
-- url     : https://prove2.me/submissions/b43311e1-48e8-43e2-9045-82798eb1704a

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
open MeasureTheory
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A finite extended-real union/grid estimate transfers exactly to real
probabilities, preserving the finite number of grid cells. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A B : Set Ω) (N : ℕ)
    (hFinite : (N : ℝ≥0∞) * P B ≠ ⊤)
    (hBound : P A ≤ (N : ℝ≥0∞) * P B) :
    P.real A ≤ (N : ℝ) * P.real B := by
  change (P A).toReal ≤ (N : ℝ) * (P B).toReal
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using
    (ENNReal.toReal_mono hFinite hBound)
