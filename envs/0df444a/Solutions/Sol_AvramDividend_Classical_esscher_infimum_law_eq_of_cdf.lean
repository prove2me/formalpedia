-- Prove2me | solution 1 for AvramDividend.Classical.esscher_infimum_law_eq_of_cdf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T14:04:54.880112+00:00
-- url     : https://prove2.me/submissions/bab0cdbe-b40d-4a74-b065-2ad44fc878cf

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Map

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- The common real CDF determines the actual perpetual infimum pushforward law. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsFiniteMeasure Q]
    (ν : Measure ℝ) (Yinf : Ω → ℝ)
    (hYmeas : Measurable Yinf)
    (hCDF : ∀ x : ℝ, Q (Yinf ⁻¹' Iic x) = ν (Iic x)) :
    Measure.map Yinf Q = ν := by
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply hYmeas measurableSet_Iic]
  exact hCDF x
