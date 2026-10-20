-- Prove2me | solution 2 for CohnElkies.upper_intervalIntegral_one_add_inv_sq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:27:46.062996+00:00
-- url     : https://prove2.me/submissions/2dc5c5c0-dea3-42fe-ad1d-0fa2d4f7aed5

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, 1 + (x ^ 2)⁻¹) =
      b - a + a⁻¹ - b⁻¹ := by
  have hpos : ∀ x ∈ Set.uIcc a b, 0 < x := by
    intro x hx; rw [Set.uIcc_of_le hab] at hx; linarith [hx.1]
  have hd : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun x : ℝ => x - x⁻¹) (1 + (x ^ 2)⁻¹) x := by
    intro x hx
    have hx := (hpos x hx).ne'
    have := (hasDerivAt_id' x).sub (hasDerivAt_inv hx)
    exact this.congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · ring
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.add continuousOn_const
    apply ContinuousOn.inv₀ (continuousOn_pow 2)
    intro x hx; exact (pow_pos (hpos x hx) 2).ne'

