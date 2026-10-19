-- Prove2me | solution 1 for CohnElkies.lowerWallisComplexLogPhase_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/f643e9df-feaa-4291-a930-262d32c8e65d

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    {a : ℝ} (ha : 0 ≤ a) :
    lowerWallisComplexLogPhase (a : ℂ) =
      1 + a * Real.log a -
        (a + 1) * Real.log (a + 1) := by
  have hcast : (a : ℂ) + 1 = ((a + 1 : ℝ) : ℂ) := by
    push_cast
    rfl
  have hnorm : ‖(a : ℂ) + 1‖ = a + 1 := by
    rw [hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ a + 1 by linarith)]
  unfold lowerWallisComplexLogPhase
  simp [Complex.mul_re, Complex.log_re, hnorm,
    abs_of_nonneg ha]
end CohnElkies
