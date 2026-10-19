-- Prove2me | solution 2 for CohnElkies.norm_fourierInv_le_integral_norm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:17:55.445189+00:00
-- url     : https://prove2.me/submissions/2da0a164-8aa3-49b4-b239-e2d94a432bb5

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


theorem solution (F : ℝ → ℂ) (v : ℝ) :
    ‖((𝓕⁻ F : ℝ → ℂ) v)‖ ≤ ∫ s : ℝ, ‖F s‖ := by
  rw [Real.fourierInv_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext s
  rw [Circle.norm_smul]

