-- Prove2me | solution 2 for CohnElkies.integral_profileNegativePart_eq_half
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:07:24.159061+00:00
-- url     : https://prove2.me/submissions/879dece4-c9b2-45b7-9825-5cc5a72a305e

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


theorem solution {φ : ℝ → ℝ}
    (hφ : Integrable φ)
    (hmean : (∫ v : ℝ, φ v) = 0)
    (hmass : (∫ v : ℝ, |φ v|) = 1) :
    (∫ v : ℝ, profileNegativePart φ v) = (1 / 2 : ℝ) := by
  have h : ∀ v, profileNegativePart φ v = (|φ v| - φ v) / 2 := by
    intro v; unfold profileNegativePart
    rcases le_total 0 (φ v) with h | h
    · rw [abs_of_nonneg h, max_eq_right (by linarith)]; ring
    · rw [abs_of_nonpos h, max_eq_left (by linarith)]; ring
  simp_rw [h]
  rw [integral_div, integral_sub hφ.abs hφ, hmass, hmean]
  norm_num

