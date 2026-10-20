-- Prove2me | solution 2 for CohnElkies.lowerRiemannLog_scaled_factor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:43:37.483508+00:00
-- url     : https://prove2.me/submissions/d0b097f0-86a6-49bf-b939-d8487b4a6719

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
    {ℓ T : ℝ} (hℓ : 0 < ℓ) (j : ℝ) :
    Real.sqrt (j ^ 2 + (ℓ * T / 2) ^ 2) =
      ℓ * Real.sqrt ((j / ℓ) ^ 2 + T ^ 2 / 4) := by
  have e : ℓ * Real.sqrt ((j / ℓ) ^ 2 + T ^ 2 / 4) = Real.sqrt (ℓ ^ 2 * ((j / ℓ) ^ 2 + T ^ 2 / 4)) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hℓ.le]
  rw [e]
  congr 1
  field_simp <;> ring

