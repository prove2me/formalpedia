-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_caplinear_ofReal_real_switch_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:44:12.162966+00:00
-- url     : https://prove2.me/submissions/0e77c826-c0e9-49db-a2d1-6077709c6bef

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal
noncomputable section

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ) (z : ℝ) :
    (if ENNReal.ofReal z ≤ C then w z
      else w C.toReal + (z - C.toReal)) =
    (if C = ⊤ then w z
      else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)) := by
  by_cases hTop : C = ⊤
  · simp [hTop]
  · have hSwitch : ENNReal.ofReal z ≤ C ↔ z ≤ C.toReal :=
      ENNReal.ofReal_le_iff_le_toReal hTop
    simp [hTop, hSwitch]
