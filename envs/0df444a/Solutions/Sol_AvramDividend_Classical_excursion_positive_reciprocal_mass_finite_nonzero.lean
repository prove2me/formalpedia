-- Prove2me | solution 1 for AvramDividend.Classical.excursion_positive_reciprocal_mass_finite_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:58:45.226752+00:00
-- url     : https://prove2.me/submissions/cc5792bb-4808-4796-9d3a-fba80c7c22aa

import Mathlib.MeasureTheory.Measure.Prokhorov
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-!
A positive real k has positive finite reciprocal. Thus a measure with
total mass ofReal (k⁻¹) is finite and nonzero, as required to normalise
the excursion resolvent approximants to probability measures.
-/
theorem solution
    (β : Measure ℝ) (k : ℝ) (hk : 0 < k)
    (hmass : β Set.univ = ENNReal.ofReal (k⁻¹)) :
    β Set.univ < ⊤ ∧ β ≠ 0 := by
  constructor
  · rw [hmass]
    exact ENNReal.ofReal_lt_top
  · intro hβ
    have hp : 0 < β Set.univ := by
      rw [hmass]
      exact ENNReal.ofReal_pos.mpr (inv_pos.mpr hk)
    simp [hβ] at hp
