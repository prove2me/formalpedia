-- Prove2me | solution 2 for CohnElkies.complexDigamma_continuousOn_positiveHalfPlane
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:57:56.590779+00:00
-- url     : https://prove2.me/submissions/45b931c7-ee10-432b-84c1-2d0b2a8d9439

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators


theorem solution :
    ContinuousOn Complex.digamma
      {z : ℂ | 0 < z.re} := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hne : ∀ z : ℂ, 0 < z.re → ∀ m : ℕ, z ≠ -m := by
    intro z hz m h; rw [h] at hz; simp at hz <;> linarith [(m.cast_nonneg : (0:ℝ) ≤ m)]
  have hd : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := fun z hz =>
    (Complex.differentiableAt_Gamma z (hne z hz)).differentiableWithinAt
  have := ((hd.deriv hU).continuousOn).div hd.continuousOn
    (fun z hz => Complex.Gamma_ne_zero_of_re_pos hz)
  refine this.congr fun z _ => ?_
  simp [Complex.digamma_def, logDeriv_apply]

