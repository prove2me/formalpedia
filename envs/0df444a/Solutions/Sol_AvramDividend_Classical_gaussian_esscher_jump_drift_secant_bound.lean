-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_jump_drift_secant_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:27:35.255433+00:00
-- url     : https://prove2.me/submissions/ed3efa14-babf-4b48-9ed1-4c61b02c399b

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The tilted single-jump drift dominates the secant of the
compensated exponential for any truncation value and shift. -/
theorem solution (φ z k : ℝ) :
    Real.exp (-φ * z) - 1 + φ * k ≤
      φ * (k - z * Real.exp (-φ * z)) := by
  let u : ℝ := φ * z
  have hlinear : 1 + u ≤ Real.exp u := by
    have h := Real.add_one_le_exp u
    linarith
  have hproduct : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add]
    simp
  have hbound : (1 + u) * Real.exp (-u) ≤ 1 := by
    calc
      _ ≤ Real.exp u * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right hlinear (Real.exp_pos _).le
      _ = 1 := hproduct
  have hbound' : (1 + φ * z) * Real.exp (-φ * z) ≤ 1 := by
    simpa only [u, neg_mul] using hbound
  nlinarith [hbound']
