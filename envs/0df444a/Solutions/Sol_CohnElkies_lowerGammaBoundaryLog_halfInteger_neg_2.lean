-- Prove2me | solution 2 for CohnElkies.lowerGammaBoundaryLog_halfInteger_neg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:34:19.010686+00:00
-- url     : https://prove2.me/submissions/e8032103-a7da-4b8e-8486-3333fa18d0e8

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology


theorem solution
    (k : ℕ) (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R (-y) =
      lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R y := by
  unfold lowerGammaBoundaryLog
  have h1 : -Complex.I * ((-y : ℝ) : ℂ) / 2 = (starRingEnd ℂ) (-Complex.I * (y : ℂ) / 2) := by
    simp only [map_div₀, map_mul, map_neg, map_add, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    push_cast; ring
  have h2 : (((k : ℝ) + 1 / 2 : ℝ) : ℂ) + Complex.I * ((-y : ℝ) : ℂ) / 2 =
      (starRingEnd ℂ) ((((k : ℝ) + 1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ) / 2) := by
    simp only [map_div₀, map_mul, map_neg, map_add, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    push_cast; ring
  rw [h1, h2, Complex.Gamma_conj, Complex.Gamma_conj, Complex.norm_conj, Complex.norm_conj]

