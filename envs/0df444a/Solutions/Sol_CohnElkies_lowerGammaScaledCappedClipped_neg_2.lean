-- Prove2me | solution 2 for CohnElkies.lowerGammaScaledCappedClipped_neg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:29:41.245979+00:00
-- url     : https://prove2.me/submissions/986ce608-0bab-4849-8c13-af93a41badb5

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology


theorem solution
    (d : ℕ) (c D n Y : ℝ) :
    lowerGammaScaledCappedClipped d c D n (-Y) =
      lowerGammaScaledCappedClipped d c D n Y := by
  have key : ∀ ℓ R y, lowerGammaBoundaryLog ℓ R (-y) = lowerGammaBoundaryLog ℓ R y := by
    intro ℓ R y
    unfold lowerGammaBoundaryLog
    have e1 : (-Complex.I * ((-y:ℝ):ℂ) / 2) = (starRingEnd ℂ) (-Complex.I * (y:ℂ) / 2) := by
      simp only [map_div₀, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
      push_cast; ring
    have e2 : ((ℓ:ℂ) + Complex.I * ((-y:ℝ):ℂ) / 2) = (starRingEnd ℂ) ((ℓ:ℂ) + Complex.I * (y:ℂ) / 2) := by
      simp only [map_add, map_div₀, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
      push_cast; ring
    rw [e1, e2, Complex.Gamma_conj, Complex.Gamma_conj, Complex.norm_conj, Complex.norm_conj]
  unfold lowerGammaScaledCappedClipped lowerGammaBoundaryCapped
  simp only [mul_neg, neg_eq_zero, key]

