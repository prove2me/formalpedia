-- Prove2me | solution 2 for CohnElkies.lowerGammaBoundaryLog_integer_neg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:08:10.464132+00:00
-- url     : https://prove2.me/submissions/f5fa9eb2-c41a-47b4-a132-8a84adc62776

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
    lowerGammaBoundaryLog (k : ℝ) R (-y) =
      lowerGammaBoundaryLog (k : ℝ) R y := by
  unfold lowerGammaBoundaryLog
  have h1 : -Complex.I * ((-y : ℝ) : ℂ) / 2 = (starRingEnd ℂ) (-Complex.I * (y : ℂ) / 2) := by
    simp only [map_div₀, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, map_ofNat,
      Complex.ofReal_neg]
    ring
  have h2 : ((k:ℝ) : ℂ) + Complex.I * ((-y : ℝ) : ℂ) / 2 =
      (starRingEnd ℂ) (((k:ℝ) : ℂ) + Complex.I * (y : ℂ) / 2) := by
    simp only [map_add, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat,
      Complex.ofReal_neg]
    ring
  rw [h1, h2, Complex.Gamma_conj, Complex.Gamma_conj, Complex.norm_conj, Complex.norm_conj]

