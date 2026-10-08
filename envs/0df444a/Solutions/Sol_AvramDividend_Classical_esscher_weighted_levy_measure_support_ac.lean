-- Prove2me | solution 1 for AvramDividend.Classical.esscher_weighted_levy_measure_support_ac
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:10:43.485299+00:00
-- url     : https://prove2.me/submissions/34db25da-7751-447f-9c76-10882037f665

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- The Esscher exponential density never creates positive jumps and
preserves absolute continuity of a negative-jump Lévy measure. -/
theorem solution
    (ν : Measure ℝ) (φ : ℝ)
    (hneg : ν (Ici 0) = 0) (hac : ν ≪ volume) :
    (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y)))) (Ici 0) = 0 ∧
    ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))) ≪ volume := by
  have hsub :
      ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))) ≪ ν :=
    withDensity_absolutelyContinuous ν
      (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y)))
  refine ⟨?_, ?_⟩
  · exact hsub hneg
  · exact hsub.trans hac
