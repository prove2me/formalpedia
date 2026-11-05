-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_assist_p3_cap_extension_deriv_eq_strict_interior
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:39:15.936045+00:00
-- url     : https://prove2.me/submissions/2e55acce-82f3-4981-b2cc-3928ddd43f06

import Mathlib.Analysis.Calculus.Deriv.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter
open scoped ENNReal Topology
noncomputable section

/-- Derivatives of the actual cap continuation agree in its strict interior. -/
theorem solution
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (z : ℝ) (hz : 0 < z ∧ ENNReal.ofReal z < C) :
    deriv V z = deriv w z := by
  by_cases hC : C = ⊤
  · have hEq : V = w := funext (hVtop hC)
    rw [hEq]
  · have hz0 : 0 ≤ z := le_of_lt hz.1
    have hne : ENNReal.ofReal z ≠ ⊤ := ENNReal.ofReal_ne_top
    have hlt : (ENNReal.ofReal z).toReal < C.toReal :=
      (ENNReal.toReal_lt_toReal hne hC).2 hz.2
    rw [ENNReal.toReal_ofReal hz0] at hlt
    have hlocal : V =ᶠ[𝓝 z] w := by
      filter_upwards [isOpen_Iio.mem_nhds hlt] with y hy
      have hV := hVfinite hC y
      rw [if_pos (le_of_lt hy)] at hV
      exact hV
    exact hlocal.deriv_eq
