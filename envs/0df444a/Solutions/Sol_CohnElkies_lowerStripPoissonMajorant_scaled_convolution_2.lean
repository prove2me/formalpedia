-- Prove2me | solution 2 for CohnElkies.lowerStripPoissonMajorant_scaled_convolution
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:02:06.839791+00:00
-- url     : https://prove2.me/submissions/3a6cc1e0-e827-4c8c-a2d0-ddab527cdc26

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
    {ℓ : ℝ} (hℓ : 0 < ℓ) (R σ s : ℝ) :
    lowerStripPoissonMajorant ℓ R σ s =
      ∫ Y : ℝ,
        stripPoissonKernel σ (s / ℓ - Y) *
          lowerGammaBoundaryLog ℓ R (ℓ * Y) := by
  unfold lowerStripPoissonMajorant
  have h := MeasureTheory.integral_sub_left_eq_self
    (fun T : ℝ => stripPoissonKernel σ T * lowerGammaBoundaryLog ℓ R (s - ℓ * T))
    MeasureTheory.volume (s / ℓ)
  rw [← h]
  congr 1
  funext Y
  congr 2
  field_simp
  ring

