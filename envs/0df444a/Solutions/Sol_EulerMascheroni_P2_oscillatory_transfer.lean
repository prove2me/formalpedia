-- Prove2me | solution 1 for EulerMascheroni.P2.oscillatory_transfer
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-12T00:03:00.145097+00:00
-- url     : https://prove2.me/submissions/05d1d287-5b0a-4592-9747-b0124ca3a82f

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-- Stability of an oscillating leading term under relative denominator error.
This is an additive estimate, so it remains valid near zeros of the leading term. -/
theorem solution (s u v : ℝ) (hs : |s| ≤ 1) (hu : |u| ≤ 1/2) :
    |(s+v)/(1+u)-s| ≤ 2 * (|v|+|u|) := by
  have hu0 : (1/2 : ℝ) ≤ 1+u := by
    have := (abs_le.mp hu).1
    linarith
  have hd : 0 < 1+u := by linarith
  have heq : (s+v)/(1+u)-s = (v-u*s)/(1+u) := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  have hnum : |v-u*s| ≤ |v|+|u| := by
    calc
      |v-u*s| ≤ |v|+|u*s| := by simpa using abs_sub_le v 0 (u*s)
      _ = |v|+|u| * |s| := by rw [abs_mul]
      _ ≤ |v|+|u| := by nlinarith [abs_nonneg u]
  nlinarith [abs_nonneg u, abs_nonneg v]

#print axioms solution
