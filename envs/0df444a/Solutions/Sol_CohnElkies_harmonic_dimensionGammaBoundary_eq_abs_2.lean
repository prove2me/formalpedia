-- Prove2me | solution 2 for CohnElkies.harmonic_dimensionGammaBoundary_eq_abs
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:02:21.069916+00:00
-- url     : https://prove2.me/submissions/42d6ac85-537e-4879-b387-f2084602f405

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology


theorem solution
    {d : ℕ} (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog ((d : ℝ) / 2) R y =
      lowerGammaBoundaryLog ((d : ℝ) / 2) R |y| := by
  have hc : ∀ s : ℂ, ‖Complex.Gamma ((starRingEnd ℂ) s)‖ = ‖Complex.Gamma s‖ := fun s => by
    rw [Complex.Gamma_conj, Complex.norm_conj]
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    unfold lowerGammaBoundaryLog
    have e1 : -Complex.I * ((-y : ℝ) : ℂ) / 2 = starRingEnd ℂ (-Complex.I * (y : ℂ) / 2) := by
      simp only [map_div₀, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
      push_cast; ring
    have e2 : (((d : ℝ) / 2 : ℝ) : ℂ) + Complex.I * ((-y : ℝ) : ℂ) / 2 =
        starRingEnd ℂ ((((d : ℝ) / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ) / 2) := by
      simp only [map_add, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
      push_cast; ring
    rw [e1, e2, hc, hc]

