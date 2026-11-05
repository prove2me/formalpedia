-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_assist_p3_cap_extension_C1_strict_interior
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:37:01.475692+00:00
-- url     : https://prove2.me/submissions/93db9ed3-a2c0-4b1b-aa8c-d69266a8afad

import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal
noncomputable section

/-- The cap-linear extension agrees with the source C1 function in its interior. -/
theorem solution
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (hw : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C}) :
    ContDiffOn ℝ 1 V
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} := by
  apply hw.congr
  intro z hz
  by_cases hC : C = ⊤
  · exact hVtop hC z
  · have hz0 : 0 ≤ z := le_of_lt hz.1
    have hne : ENNReal.ofReal z ≠ ⊤ := ENNReal.ofReal_ne_top
    have hlt : (ENNReal.ofReal z).toReal < C.toReal :=
      (ENNReal.toReal_lt_toReal hne hC).2 hz.2
    have hzcap : z ≤ C.toReal := by
      rw [ENNReal.toReal_ofReal hz0] at hlt
      exact le_of_lt hlt
    have hzV := hVfinite hC z
    rw [if_pos hzcap] at hzV
    exact hzV
