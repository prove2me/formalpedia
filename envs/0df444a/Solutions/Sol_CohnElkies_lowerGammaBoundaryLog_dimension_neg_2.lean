-- Prove2me | solution 2 for CohnElkies.lowerGammaBoundaryLog_dimension_neg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:24:29.707919+00:00
-- url     : https://prove2.me/submissions/7ceec444-6184-48f6-82d8-7a0fa62ea9d9

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
    {d : ℕ} (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog ((d : ℝ) / 2) R (-y) =
      lowerGammaBoundaryLog ((d : ℝ) / 2) R y := by
  unfold lowerGammaBoundaryLog
  have h2c : (starRingEnd ℂ) 2 = 2 := by apply Complex.ext <;> simp
  have h1 : -Complex.I * (((-y:ℝ)):ℂ) / 2 = (starRingEnd ℂ) (-Complex.I * (y:ℂ) / 2) := by
    apply Complex.ext <;> simp [h2c]
  have h2 : (((d:ℝ)/2 : ℝ) : ℂ) + Complex.I * (((-y:ℝ)):ℂ) / 2 = (starRingEnd ℂ) ((((d:ℝ)/2 : ℝ) : ℂ) + Complex.I * (y:ℂ) / 2) := by
    apply Complex.ext <;> simp [h2c]
  rw [h1, h2, Complex.Gamma_conj, Complex.Gamma_conj, Complex.norm_conj, Complex.norm_conj]

